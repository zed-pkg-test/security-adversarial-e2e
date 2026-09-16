use std::{env, fs, path::PathBuf, process};

use ores_api_docs::{materialize_finalized_page_build, write_page_build_outputs};

fn main() {
    tampered_finalized_css_must_fail_closed();
    println!("zed-pkg-test finalized asset integrity certification passed");
}

fn tampered_finalized_css_must_fail_closed() {
    let root = fresh_root();
    let page_dir = root.join("src/pages");
    fs::create_dir_all(&page_dir).expect("create page dir");
    fs::write(
        page_dir.join("page.rs"),
        r#"#[ores_page(renderer = "mash", delivery = "ssr_only")]
pub async fn page() {}
"#,
    )
    .expect("write page");
    fs::write(page_dir.join("style.css"), b"body { color: green; }\n").expect("write css");

    let first_pass = root.join(".ores-stack/first-pass");
    let outputs = write_page_build_outputs(&root, &first_pass).expect("first pass");
    let asset_dir = first_pass.join("page-assets");
    let asset_name = fs::read_dir(&asset_dir)
        .expect("read asset dir")
        .next()
        .expect("generated css entry")
        .expect("generated css direntry")
        .file_name();
    let asset_path = asset_dir.join(asset_name);

    fs::write(&asset_path, b"body { color: red; }\n").expect("tamper finalized css");

    let materialized = root.join(".ores-stack/materialized");
    let error = materialize_finalized_page_build(
        &root,
        &materialized,
        &outputs.manifest_path,
        &asset_dir,
    )
    .expect_err("digest drift in finalized CSS must fail closed");
    let message = error.to_string().to_lowercase();
    assert!(
        message.contains("digest") || message.contains("sha256") || message.contains("hash"),
        "unexpected integrity error: {message}"
    );
    cleanup(root);
}

fn fresh_root() -> PathBuf {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock")
        .as_nanos();
    let root = env::temp_dir().join(format!(
        "zed-ores-finalized-asset-integrity-{}-{now}",
        process::id()
    ));
    if root.exists() {
        fs::remove_dir_all(&root).expect("clear stale fixture");
    }
    root
}

fn cleanup(root: PathBuf) {
    fs::remove_dir_all(root).expect("cleanup fixture");
}
