// Code that is available both for build hooks, and for the main program.
// Don't use crate stuff in here.

use std::error::Error;
use std::fs;
use std::path::PathBuf;

pub fn files_dir() -> PathBuf {
    let d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.join("files")
}

// Finds the most recent onnx model file.
pub fn most_recent_onnx_model() -> Result<PathBuf, Box<dyn Error>> {
    let d = files_dir().join("models");

    // Naming is by timestamp, so the largest is the most recent
    let filename = match fs::read_dir(d.clone())?
        .filter_map(|entry| entry.ok())
        .filter_map(|entry| {
            let path = entry.path();
            if let Some(filename) = path.file_name()?.to_str() {
                if filename.starts_with("model-") && filename.ends_with(".onnx") {
                    return Some(filename.to_string());
                }
            }
            None
        })
        .max()
    {
        Some(filename) => filename,
        None => return Err("No model files found".into()),
    };
    Ok(d.join(filename))
}
