use ariadne::{Color, Label, Report, ReportKind, Source};
use ast::Location;
use thiserror::Error;

#[derive(Error, Debug, PartialEq)]
pub enum TypeCheckError {
    #[error("Type mismatch: expected {expected}, found {found}")]
    TypeMismatch {
        expected: String,
        found: String,
        location: Location,
    },
    #[error("Undefined identifier: {name}")]
    UndefinedIdentifier { name: String, location: Location },
    #[error("Uninitialized variable use: {name}")]
    UninitializedVariable { name: String, location: Location },
    #[error("Assignment to immutable variable: {name}")]
    AssignmentToImmutable { name: String, location: Location },
    #[error("Function call argument mismatch")]
    FunctionCallArgumentMismatch { location: Location },
    #[error("Duplicate definition: {name}")]
    DuplicateDefinition { name: String, location: Location },
    #[error("Expression must be last in block")]
    ExpressionMustBeLastInBlock { location: Location },
    #[error("Invalid operator: {operator}")]
    InvalidOperator {
        operator: String,
        location: Location,
    },
}

impl TypeCheckError {
    pub fn format(&self, source_id: &str, source: &str) -> String {
        let mut report = Report::build(ReportKind::Error, source_id, 0);

        match self {
            TypeCheckError::TypeMismatch {
                expected,
                found,
                location,
            } => {
                report = report
                    .with_message(format!("Type mismatch: expected {expected}, found {found}"))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("Expected {expected} but found {found}"))
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::UndefinedIdentifier { name, location } => {
                report = report
                    .with_message(format!("Undefined identifier: {name}"))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("'{name}' is not defined"))
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::UninitializedVariable { name, location } => {
                report = report
                    .with_message(format!("Use of uninitialized variable: {name}"))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("'{name}' used before being initialized"))
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::AssignmentToImmutable { name, location } => {
                report = report
                    .with_message(format!("Assignment to immutable variable: {name}"))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("'{name}' is immutable and cannot be assigned"))
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::FunctionCallArgumentMismatch { location } => {
                report = report
                    .with_message("Function call argument mismatch")
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message("Argument count or types don't match function signature")
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::DuplicateDefinition { name, location } => {
                report = report
                    .with_message(format!("Duplicate definition: {name}"))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("'{name}' is already defined"))
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::ExpressionMustBeLastInBlock { location } => {
                report = report
                    .with_message("Expression must be last in block")
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(
                                "An expression statement must be the last statement in a block",
                            )
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::InvalidOperator { operator, location } => {
                report = report
                    .with_message(format!("Invalid operator: {operator}"))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!(
                                "Operator '{operator}' is not valid in this context"
                            ))
                            .with_color(Color::Red),
                    );
            }
        }

        let mut result = Vec::new();
        report
            .finish()
            .write((source_id, Source::from(source)), &mut result)
            .unwrap();
        String::from_utf8(result).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeChecker;

    #[test]
    fn test_error_formatting() {
        let checker = TypeChecker::new();
        let error = TypeCheckError::TypeMismatch {
            expected: "i32".to_string(),
            found: "i64".to_string(),
            location: ast::Location {
                start: 10,
                end: 15,
                context: (),
            },
        };

        let source = "let x: i32 = 42i64;";
        let formatted = checker.format_error(&error, "test.ao", source);

        // Just verify that the error formatting doesn't panic and contains key information
        assert!(formatted.contains("Type mismatch"));
        assert!(formatted.contains("i32"));
        assert!(formatted.contains("i64"));
    }

    #[test]
    fn test_error_reporting_with_real_source() {
        let checker = TypeChecker::new();

        let source = "let x: i32 = 42i64;"; // Type mismatch error

        // Create a type error with realistic source locations
        let error = TypeCheckError::TypeMismatch {
            expected: "i32".to_string(),
            found: "i64".to_string(),
            location: ast::Location {
                start: 13,
                end: 18,
                context: (),
            }, // "42i64" position
        };

        let formatted = checker.format_error(&error, "test.ao", source);

        // Verify the error message contains the expected information
        assert!(formatted.contains("Type mismatch"));
        assert!(formatted.contains("i32"));
        assert!(formatted.contains("i64"));
        assert!(formatted.contains("test.ao"));

        // Print the formatted error to see how it looks
        println!("Formatted error:\n{formatted}");
    }
}
