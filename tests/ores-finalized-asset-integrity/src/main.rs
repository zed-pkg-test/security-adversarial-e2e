use std::{env, fs, path::PathBuf, process};

use ores_api_docs::{
    materialize_finalized_page_build, read_page_build_manifest, write_page_build_manifest,
    write_page_build_outputs,
};
use sha2::{Digest, Sha256};

fn main() {
    tampered_finalized_css_must_fail_closed();
    finalized_browser_assets_materialize_when_untampered();
    tampered_finalized_js_must_fail_closed();
    tampered_finalized_wasm_must_fail_closed();
    println!("zed-pkg-test finalized asset integrity certification passed");
}

fn tampered_finalized_css_must_fail_closed() {
    let root = fresh_root("css");
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
    let error =
        materialize_finalized_page_build(&root, &materialized, &outputs.manifest_path, &asset_dir)
            .expect_err("digest drift in finalized CSS must fail closed");
    assert_integrity_error(&error.to_string());
    cleanup(root);
}

fn finalized_browser_assets_materialize_when_untampered() {
    let fixture = browser_fixture("browser-good");
    materialize_finalized_page_build(
        &fixture.root,
        &fixture.root.join(".ores-stack/materialized"),
        &fixture.manifest_path,
        &fixture.asset_dir,
    )
    .expect("untampered finalized browser assets must materialize");
    cleanup(fixture.root);
}

fn tampered_finalized_js_must_fail_closed() {
    let fixture = browser_fixture("browser-js-tamper");
    fs::write(&fixture.js_path, b"console.log('tampered');\n").expect("tamper js");
    let error = materialize_finalized_page_build(
        &fixture.root,
        &fixture.root.join(".ores-stack/materialized"),
        &fixture.manifest_path,
        &fixture.asset_dir,
    )
    .expect_err("digest drift in finalized JS must fail closed");
    assert_integrity_error(&error.to_string());
    cleanup(fixture.root);
}

fn tampered_finalized_wasm_must_fail_closed() {
    let fixture = browser_fixture("browser-wasm-tamper");
    fs::write(&fixture.wasm_path, b"tampered-wasm").expect("tamper wasm");
    let error = materialize_finalized_page_build(
        &fixture.root,
        &fixture.root.join(".ores-stack/materialized"),
        &fixture.manifest_path,
        &fixture.asset_dir,
    )
    .expect_err("digest drift in finalized WASM must fail closed");
    assert_integrity_error(&error.to_string());
    cleanup(fixture.root);
}

struct BrowserFixture {
    root: PathBuf,
    manifest_path: PathBuf,
    asset_dir: PathBuf,
    js_path: PathBuf,
    wasm_path: PathBuf,
}

fn browser_fixture(suffix: &str) -> BrowserFixture {
    let root = fresh_root(suffix);
    let page_dir = root.join("src/pages/dashboard");
    fs::create_dir_all(&page_dir).expect("create browser page dir");
    fs::write(
        page_dir.join("page.rs"),
        r#"#[ores_page(
renderer = "leptos",
delivery = "ssr_hydrate",
client = "client.rs"
)]
pub async fn page() {}
"#,
    )
    .expect("write browser page");
    fs::write(page_dir.join("client.rs"), b"pub fn hydrate() {}\n").expect("write client");

    let first_pass = root.join(".ores-stack/first-pass");
    let outputs = write_page_build_outputs(&root, &first_pass).expect("browser first pass");
    let asset_dir = first_pass.join("page-assets");
    let mut manifest = read_page_build_manifest(&outputs.manifest_path).expect("read manifest");
    let wasm = manifest.routes[0].wasm.as_mut().expect("wasm plan");

    let wasm_bytes = b"valid-wasm-bytes";
    let js_bytes = b"console.log('valid');\n";
    let wasm_sha256 = sha256_hex(wasm_bytes);
    let js_sha256 = sha256_hex(js_bytes);
    let wasm_file = format!("page-{wasm_sha256}.wasm");
    let js_file = format!("page-{js_sha256}.js");
    let wasm_path = asset_dir.join(&wasm_file);
    let js_path = asset_dir.join(&js_file);
    fs::write(&wasm_path, wasm_bytes).expect("write finalized wasm");
    fs::write(&js_path, js_bytes).expect("write finalized js");

    wasm.final_wasm_sha256 = Some(wasm_sha256);
    wasm.wasm_output_file = Some(wasm_file.clone());
    wasm.public_path = Some(format!("/__ores/assets/{wasm_file}"));
    wasm.js_sha256 = Some(js_sha256);
    wasm.js_output_file = Some(js_file.clone());
    wasm.js_public_path = Some(format!("/__ores/assets/{js_file}"));
    write_page_build_manifest(&outputs.manifest_path, &manifest).expect("write finalized manifest");

    BrowserFixture {
        root,
        manifest_path: outputs.manifest_path,
        asset_dir,
        js_path,
        wasm_path,
    }
}

fn assert_integrity_error(message: &str) {
    let message = message.to_lowercase();
    assert!(
        message.contains("digest") || message.contains("sha256") || message.contains("hash"),
        "unexpected integrity error: {message}"
    );
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn fresh_root(suffix: &str) -> PathBuf {
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock")
        .as_nanos();
    let root = env::temp_dir().join(format!(
        "zed-ores-finalized-asset-integrity-{}-{now}-{suffix}",
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
