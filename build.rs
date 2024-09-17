use burn_import::onnx::{ModelGen, RecordType};

include!("src/common.rs");

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=files/models/");

    let onnx_filename = most_recent_onnx_model().unwrap();

    println!("cargo:warning=Compiling model: {}", onnx_filename.display());

    // Clear out the burn directory
    let out_dir = files_dir().join("burn");
    for entry in fs::read_dir(out_dir.clone()).unwrap() {
        let path = entry.unwrap().path();

        // Skip the readme
        if path.ends_with("README.md") {
            continue;
        }

        // Check if it's a file and delete it
        if path.is_file() {
            fs::remove_file(path).expect("Could not remove file");
        }
    }

    // Make a copy so that we have a sane name
    let tmp_onnx = out_dir.join("model.onnx");
    fs::copy(onnx_filename.clone(), tmp_onnx.clone()).expect("Could not copy file");

    ModelGen::new()
        .input(tmp_onnx.to_str().unwrap())
        .out_dir(out_dir.to_str().unwrap())
        .record_type(RecordType::Bincode)
        .embed_states(true)
        .run_from_script();

    println!("cargo:warning=Model compiled.");
}
