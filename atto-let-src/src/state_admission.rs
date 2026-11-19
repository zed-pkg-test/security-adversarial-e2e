//! Bounded non-parking scheduler admission policy for *future* shared state.
//!
//! This model is not wired into the single-Worker compiler's Wasm guest ABI.
//! No guest code executes while this state machine mutates. All operations
//! are bounded by N and allocate no storage after the Gate is constructed.
//! Ticket identities MUST originate at a trusted scheduler boundary.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode { Read, Write }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ticket {
    pub container: u64,
    pub actor_incarnation: u64,
    pub epoch: u64,
    pub invocation: u64,
    pub continuation: u64,
    pub mode: Mode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Admission { Granted(Ticket), Queued(Ticket) }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Retired, Full, Exhausted, StaleTicket, NotGranted,
    AlreadyActive, ReadToWriteUpgrade, RunningNeedsCompletion,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase { Queued, Granted, Running }

#[derive(Clone, Copy, Debug)]
struct Entry { ticket: Ticket, phase: Phase }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Snapshot {
    pub queued: usize,
    pub granted: usize,
    pub running: usize,
    pub readers: usize,
    pub writers: usize,
    pub retired: bool,
}

/// One logical admission domain. Thread identities do not determine ownership;
/// the caller supplies a scheduler-authenticated continuation + incarnation.
pub struct Gate<const N: usize> {
    container: u64,
    actor_incarnation: u64,
    epoch: u64,
    next: u64,
    retired: bool,
    slots: [Option<Entry>; N],
}

impl<const N: usize> Gate<N> {
    /// Compatibility constructor for a single local admission domain.
    /// Production runtimes should call with_identity using host-owned IDs.
    pub const fn new(epoch: u64) -> Self {
        Self::with_identity(0, 0, epoch)
    }

    /// The host/scheduler owns these identities; never accept them from a
    /// guest or from a caller who can forge an actor's continuation.
    pub const fn with_identity(container: u64, actor_incarnation: u64, epoch: u64) -> Self {
        Self { container, actor_incarnation, epoch, next: 0,
               retired: false, slots: [None; N] }
    }

    pub fn snapshot(&self) -> Snapshot {
        let mut s = Snapshot {
            queued: 0, granted: 0, running: 0,
            readers: 0, writers: 0, retired: self.retired,
        };
        for entry in self.slots.iter().flatten() {
            match entry.phase {
                Phase::Queued => s.queued += 1,
                Phase::Granted => s.granted += 1,
                Phase::Running => s.running += 1,
            }
            if entry.phase != Phase::Queued {
                match entry.ticket.mode {
                    Mode::Read => s.readers += 1,
                    Mode::Write => s.writers += 1,
                }
            }
        }
        s
    }

    pub fn request(&mut self, continuation: u64, mode: Mode) -> Result<Admission, Error> {
        if self.retired { return Err(Error::Retired); }
        for entry in self.slots.iter().flatten() {
            if entry.ticket.continuation == continuation {
                return Err(if entry.ticket.mode == Mode::Read && mode == Mode::Write {
                    Error::ReadToWriteUpgrade
                } else {
                    // Reentrance needs a lexical depth token; never silently
                    // inherit another ticket or invoke a second admission.
                    Error::AlreadyActive
                });
            }
        }
        let idx = self.slots.iter().position(Option::is_none).ok_or(Error::Full)?;
        let next = self.next.checked_add(1).ok_or(Error::Exhausted)?;
        let active = self.snapshot();
        let grant = active.queued == 0 && match mode {
            Mode::Read => active.writers == 0,
            Mode::Write => active.readers == 0 && active.writers == 0,
        };
        self.next = next;
        let ticket = Ticket {
            container: self.container, actor_incarnation: self.actor_incarnation,
            epoch: self.epoch, invocation: next, continuation, mode,
        };
        self.slots[idx] = Some(Entry {
            ticket, phase: if grant { Phase::Granted } else { Phase::Queued },
        });
        Ok(if grant { Admission::Granted(ticket) } else { Admission::Queued(ticket) })
    }

    fn find(&self, ticket: Ticket) -> Result<usize, Error> {
        // A caller cannot substitute another continuation or incarnation.
        self.slots.iter().position(|slot| slot.as_ref()
            .is_some_and(|entry| entry.ticket == ticket))
            .ok_or(Error::StaleTicket)
    }

    /// A scheduler may start a granted ticket once; a queued request does
    /// not authorize execution. Retire wins any later start attempt.
    pub fn start(&mut self, ticket: Ticket) -> Result<(), Error> {
        if self.retired { return Err(Error::Retired); }
        let idx = self.find(ticket)?;
        if self.slots[idx].unwrap().phase != Phase::Granted {
            return Err(Error::NotGranted);
        }
        self.slots[idx].as_mut().unwrap().phase = Phase::Running;
        Ok(())
    }

    /// Queue cancellation and granted-but-not-yet-running cancellation
    /// revoke authority. A running physical turn MUST finish itself.
    pub fn cancel(&mut self, ticket: Ticket) -> Result<(), Error> {
        let idx = self.find(ticket)?;
        if self.slots[idx].unwrap().phase == Phase::Running {
            return Err(Error::RunningNeedsCompletion);
        }
        self.slots[idx] = None;
        self.promote();
        Ok(())
    }

    /// Called only after the *physical* turn completes. A cancellation
    /// request is not physical completion, and cannot release running work.
    pub fn finish(&mut self, ticket: Ticket) -> Result<(), Error> {
        let idx = self.find(ticket)?;
        if self.slots[idx].unwrap().phase != Phase::Running {
            return Err(Error::NotGranted);
        }
        self.slots[idx] = None;
        self.promote();
        Ok(())
    }

    /// Monotonic admission fence. Cancels all queued and granted tickets;
    /// running tickets retain lifetime pins until their physical finish.
    pub fn begin_retire(&mut self) {
        self.retired = true;
        for slot in &mut self.slots {
            if slot.as_ref().is_some_and(|e| e.phase != Phase::Running) {
                *slot = None;
            }
        }
    }

    pub fn quiescent(&self) -> bool {
        self.retired && self.slots.iter().all(Option::is_none)
    }

    fn promote(&mut self) {
        if self.retired { return; }
        loop {
            let first = self.slots.iter().enumerate()
                .filter_map(|(i, e)| e.as_ref()
                    .filter(|e| e.phase == Phase::Queued)
                    .map(|e| (i, e.ticket.invocation)))
                .min_by_key(|(_, invocation)| *invocation);
            let Some((idx, _)) = first else { return; };
            let status = self.snapshot();
            let mode = self.slots[idx].unwrap().ticket.mode;
            let eligible = match mode {
                Mode::Read => status.writers == 0,
                Mode::Write => status.writers == 0 && status.readers == 0,
            };
            if !eligible { return; }
            self.slots[idx].as_mut().unwrap().phase = Phase::Granted;
            if mode == Mode::Write { return; }
            // A head reader cohort may enter before a queued writer, but
            // new readers behind that writer cannot bypass its barrier.
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ticket(a: Admission) -> Ticket {
        match a { Admission::Granted(t) | Admission::Queued(t) => t }
    }

    #[test]
    fn parallel_readers_and_exclusive_writer() {
        let mut g = Gate::<8>::new(42);
        let a = g.request(1, Mode::Read).unwrap();
        let b = g.request(2, Mode::Read).unwrap();
        assert!(matches!(a, Admission::Granted(_)));
        assert!(matches!(b, Admission::Granted(_)));
        g.start(ticket(a)).unwrap(); g.start(ticket(b)).unwrap();
        let w = g.request(3, Mode::Write).unwrap();
        assert!(matches!(w, Admission::Queued(_)));
        assert_eq!(g.start(ticket(w)), Err(Error::NotGranted));
        g.finish(ticket(a)).unwrap();
        assert_eq!(g.snapshot().writers, 0);
        g.finish(ticket(b)).unwrap();
        assert_eq!(g.snapshot().writers, 1);
        g.start(ticket(w)).unwrap();
        assert_eq!(g.snapshot().running, 1);
        g.finish(ticket(w)).unwrap();
    }

    #[test]
    fn writer_cohort_fairness_and_no_read_bypass() {
        let mut g = Gate::<8>::new(8);
        let read_a = ticket(g.request(1, Mode::Read).unwrap());
        let writer = ticket(g.request(2, Mode::Write).unwrap());
        let read_b = ticket(g.request(3, Mode::Read).unwrap());
        let read_c = ticket(g.request(4, Mode::Read).unwrap());
        assert_eq!(g.start(read_b), Err(Error::NotGranted));
        g.start(read_a).unwrap(); g.finish(read_a).unwrap();
        assert_eq!(g.snapshot().writers, 1);
        assert_eq!(g.snapshot().queued, 2);
        assert_eq!(g.start(read_b), Err(Error::NotGranted));
        g.start(writer).unwrap(); g.finish(writer).unwrap();
        assert_eq!(g.snapshot().readers, 2);
        g.start(read_b).unwrap(); g.start(read_c).unwrap();
        g.finish(read_b).unwrap(); g.finish(read_c).unwrap();
    }

    #[test]
    fn cancellation_revokes_queued_and_granted_without_replay() {
        let mut g = Gate::<4>::new(1);
        let active = ticket(g.request(1, Mode::Write).unwrap());
        let queued = ticket(g.request(2, Mode::Read).unwrap());
        g.cancel(queued).unwrap();
        assert_eq!(g.start(queued), Err(Error::StaleTicket));
        g.start(active).unwrap();
        assert_eq!(g.cancel(active), Err(Error::RunningNeedsCompletion));
        g.finish(active).unwrap();
        assert_eq!(g.finish(active), Err(Error::StaleTicket));
        let granted = ticket(g.request(3, Mode::Write).unwrap());
        g.cancel(granted).unwrap();
        assert_eq!(g.start(granted), Err(Error::StaleTicket));
    }

    #[test]
    fn retiring_fences_queued_and_granted_but_waits_for_physical_completion() {
        let mut g = Gate::<4>::new(9);
        let running = ticket(g.request(1, Mode::Read).unwrap());
        g.start(running).unwrap();
        let granted = ticket(g.request(2, Mode::Read).unwrap());
        let queued = ticket(g.request(3, Mode::Write).unwrap());
        g.begin_retire();
        g.begin_retire();
        assert_eq!(g.request(4, Mode::Read), Err(Error::Retired));
        assert_eq!(g.start(granted), Err(Error::Retired));
        assert_eq!(g.start(queued), Err(Error::Retired));
        assert!(!g.quiescent());
        g.finish(running).unwrap();
        assert!(g.quiescent());
        assert_eq!(g.finish(running), Err(Error::StaleTicket));
    }

    #[test]
    fn ticket_identity_epoch_and_upgrade_fail_closed() {
        let mut g = Gate::<4>::new(77);
        let a = ticket(g.request(10, Mode::Read).unwrap());
        assert_eq!(g.request(10, Mode::Write), Err(Error::ReadToWriteUpgrade));
        assert_eq!(g.request(10, Mode::Read), Err(Error::AlreadyActive));
        assert_eq!(g.start(Ticket { epoch: 78, ..a }), Err(Error::StaleTicket));
        assert_eq!(g.start(Ticket { container: 1, ..a }), Err(Error::StaleTicket));
        assert_eq!(g.start(Ticket { actor_incarnation: 1, ..a }), Err(Error::StaleTicket));
        assert_eq!(g.start(Ticket { continuation: 11, ..a }), Err(Error::StaleTicket));
        assert_eq!(g.start(Ticket { mode: Mode::Write, ..a }), Err(Error::StaleTicket));
        g.cancel(a).unwrap();
        let b = ticket(g.request(10, Mode::Read).unwrap());
        assert_ne!(a.invocation, b.invocation);
        assert_eq!(g.start(a), Err(Error::StaleTicket));
    }

    #[test]
    fn same_epoch_and_continuation_in_other_containers_cannot_reuse_ticket() {
        let mut x = Gate::<2>::with_identity(1, 7, 55);
        let mut y = Gate::<2>::with_identity(2, 7, 55);
        let mut restarted_actor = Gate::<2>::with_identity(1, 8, 55);
        let a = ticket(x.request(5, Mode::Write).unwrap());
        let b = ticket(y.request(5, Mode::Write).unwrap());
        assert_eq!(a.invocation, b.invocation);
        assert_ne!(a, b);
        assert_eq!(y.start(a), Err(Error::StaleTicket));
        assert_eq!(restarted_actor.start(a), Err(Error::StaleTicket));
        x.start(a).unwrap();
        x.finish(a).unwrap();
    }

    #[test]
    fn bounded_capacity_does_not_allocate_or_overadmit() {
        let mut g = Gate::<2>::new(1);
        let a = ticket(g.request(1, Mode::Write).unwrap());
        let b = ticket(g.request(2, Mode::Read).unwrap());
        assert_eq!(g.request(3, Mode::Read), Err(Error::Full));
        g.cancel(b).unwrap();
        g.start(a).unwrap(); g.finish(a).unwrap();
        assert_eq!(g.snapshot().queued, 0);
        assert_eq!(Gate::<0>::new(1).request(1, Mode::Read), Err(Error::Full));
    }

    #[test]
    fn deterministic_writer_fairness_under_hot_read_stream() {
        let mut g = Gate::<16>::new(55);
        let first = ticket(g.request(1, Mode::Read).unwrap());
        g.start(first).unwrap();
        let writer = ticket(g.request(2, Mode::Write).unwrap());
        let mut readers = [None; 12];
        for (i, entry) in readers.iter_mut().enumerate() {
            let t = ticket(g.request(3 + i as u64, Mode::Read).unwrap());
            assert_eq!(g.start(t), Err(Error::NotGranted));
            *entry = Some(t);
        }
        g.finish(first).unwrap();
        assert_eq!(g.snapshot().writers, 1);
        g.start(writer).unwrap(); g.finish(writer).unwrap();
        assert_eq!(g.snapshot().readers, readers.len());
        for reader in readers.into_iter().flatten() {
            g.start(reader).unwrap(); g.finish(reader).unwrap();
        }
        assert_eq!(g.snapshot().running, 0);
    }
}
