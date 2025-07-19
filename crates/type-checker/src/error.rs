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
        }

        let mut result = Vec::new();
        report
            .finish()
            .write((source_id, Source::from(source)), &mut result)
            .unwrap();
        String::from_utf8(result).unwrap()
    }
}