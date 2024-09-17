use burn_import::onnx::ModelGen;

include!("src/common.rs");

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

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

    ModelGen::new()
        .input(onnx_filename.to_str().unwrap())
        .out_dir(out_dir.to_str().unwrap())
        .run_from_script();

    println!("cargo:warning=Model compiled.");
}
