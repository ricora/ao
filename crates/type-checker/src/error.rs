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
    InvalidOperator { operator: String, location: Location },
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
                    .with_message(format!(
                        "Type mismatch: expected {}, found {}",
                        expected, found
                    ))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("Expected {} but found {}", expected, found))
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::UndefinedIdentifier { name, location } => {
                report = report
                    .with_message(format!("Undefined identifier: {}", name))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("'{}' is not defined", name))
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::UninitializedVariable { name, location } => {
                report = report
                    .with_message(format!("Use of uninitialized variable: {}", name))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("'{}' used before being initialized", name))
                            .with_color(Color::Red),
                    );
            }
            TypeCheckError::AssignmentToImmutable { name, location } => {
                report = report
                    .with_message(format!("Assignment to immutable variable: {}", name))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("'{}' is immutable and cannot be assigned", name))
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
                    .with_message(format!("Duplicate definition: {}", name))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("'{}' is already defined", name))
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
                    .with_message(format!("Invalid operator: {}", operator))
                    .with_label(
                        Label::new((source_id, location.to_range()))
                            .with_message(format!("Operator '{}' is not valid in this context", operator))
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
        println!("Formatted error:\n{}", formatted);
    }

    #[test]
    fn test_duplicate_variable_error_with_parser() {
        use parser;

        let mut checker = TypeChecker::new();

        let source = r#"
            fn test() -> i32 {
                let x: i32 = 1;
                let x: i32 = 2;
                x
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];

        let result = checker.check_function_definition(function);

        if let Err(error) = result {
            match &error {
                TypeCheckError::DuplicateDefinition { name, .. } => {
                    assert_eq!(name, "x");

                    // Test error formatting
                    let formatted = checker.format_error(&error, "test.ao", source);
                    assert!(formatted.contains("Duplicate definition"));
                    assert!(formatted.contains("already defined"));
                    println!("Duplicate variable error:\n{}", formatted);
                }
                _ => panic!("Expected duplicate definition error, got: {:?}", error),
            }
        } else {
            panic!("Expected error for duplicate variable definition");
        }
    }
}