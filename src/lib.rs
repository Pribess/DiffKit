#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_public;

pub mod diff;
pub mod engine;
pub mod graph;
pub mod language;
pub mod model;
pub mod render;

pub type DiffkitResult<T> = std::result::Result<T, Box<dyn std::error::Error + Send + Sync>>;

pub use engine::{
    DiffReport, OcamlDiffOptions, RustAnalysisMode, RustDiffOptions, ocamldiff_paths,
    ocamldiff_sources, rustdiff_paths, rustdiff_sources,
};
pub use render::{ColorMode, RenderOptions, render_report, render_report_with_options};
