pub mod checker;
pub mod env;
pub mod error;

// Re-export main types for convenience
pub use checker::TypeChecker;
pub use env::{Type, TypeEnvironment, VariableInfo, FunctionInfo};
pub use error::TypeCheckError;