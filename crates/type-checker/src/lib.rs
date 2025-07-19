pub mod checker;
pub mod env;
pub mod error;

// Re-export main types for convenience
pub use checker::TypeChecker;
pub use env::{Type, TypeEnvironment, VariableInfo, FunctionInfo};
pub use error::TypeCheckError;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_environment_creation() {
        let env = TypeEnvironment::new();
        assert_eq!(env.variable_scopes.len(), 1); // Should have global scope
        assert!(env.functions.is_empty());
    }

    #[test]
    fn test_add_variable_to_environment() {
        let mut env = TypeEnvironment::new();
        env.add_variable(
            "x".to_string(),
            VariableInfo {
                var_type: Type::I32,
                mutable: false,
                initialized: true,
            },
        );

        let var_info = env.get_variable("x").unwrap();
        assert_eq!(var_info.var_type, Type::I32);
        assert!(!var_info.mutable);
        assert!(var_info.initialized);
    }

    #[test]
    fn test_check_integer_literal() {
        use ast::{IntegerLiteral, Location};

        let checker = TypeChecker::new();
        let literal = IntegerLiteral {
            value: "42",
            location: Location {
                start: 0,
                end: 2,
                context: (),
            },
        };

        let result = checker.check_integer_literal(&literal);
        assert_eq!(result.unwrap(), Type::I32);
    }

    #[test]
    fn test_check_binary_expression_arithmetic() {
        use ast::{BinaryExpression, Expression, IntegerLiteral, Location, Operator, OperatorKind};

        let checker = TypeChecker::new();

        let left = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "1",
            location: Location {
                start: 0,
                end: 1,
                context: (),
            },
        }));

        let right = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "2",
            location: Location {
                start: 4,
                end: 5,
                context: (),
            },
        }));

        let binary_expr = BinaryExpression {
            left,
            operator: Operator {
                operator: OperatorKind::Add,
                location: Location {
                    start: 2,
                    end: 3,
                    context: (),
                },
            },
            right,
            location: Location {
                start: 0,
                end: 5,
                context: (),
            },
        };

        let result = checker.check_binary_expression(&binary_expr);
        assert_eq!(result.unwrap(), Type::I32);
    }

    #[test]
    fn test_check_variable_definition() {
        use parser;

        let mut checker = TypeChecker::new();

        // Parse actual source code
        let source = "fn main() -> i32 { let x: i32 = 42; x }";
        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];
        let statements = &function.body.statements.statements;

        // Extract the variable definition from the parsed AST
        if let ast::Statement::VariableDefinition(var_def) = &statements[0] {
            let result = checker.check_variable_definition(&var_def);
            assert!(result.is_ok());

            // Check that variable was added to environment
            let var_info = checker.environment.get_variable("x").unwrap();
            assert_eq!(var_info.var_type, Type::I32);
            assert!(!var_info.mutable);
            assert!(var_info.initialized);
        } else {
            panic!("Expected variable definition");
        }
    }

    #[test]
    fn test_check_function_definition() {
        use parser;

        let mut checker = TypeChecker::new();

        // Parse actual source code
        let source = "fn add(x: i32, y: i32) -> i32 { 42 }";
        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let func_def = &program.functions[0];

        let result = checker.check_function_definition(func_def);
        assert!(result.is_ok());

        // Check that function was added to environment
        let func_info = checker.environment.get_function("add").unwrap();
        assert_eq!(func_info.parameters, vec![Type::I32, Type::I32]);
        assert_eq!(func_info.return_type, Type::I32);
    }

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
    fn test_block_scoping() {
        let mut checker = TypeChecker::new();

        // Add variable 'x' in outer scope
        checker.environment.push_scope();
        checker.environment.add_variable(
            "x".to_string(),
            VariableInfo {
                var_type: Type::I32,
                mutable: false,
                initialized: true,
            },
        );

        // Enter inner scope
        checker.environment.push_scope();
        checker.environment.add_variable(
            "y".to_string(),
            VariableInfo {
                var_type: Type::I64,
                mutable: false,
                initialized: true,
            },
        );

        // Both variables should be accessible
        assert!(checker.environment.get_variable("x").is_some());
        assert!(checker.environment.get_variable("y").is_some());

        // Exit inner scope
        checker.environment.pop_scope();

        // Only outer variable should be accessible
        assert!(checker.environment.get_variable("x").is_some());
        assert!(checker.environment.get_variable("y").is_none());

        checker.environment.pop_scope();
    }

    #[test]
    fn test_nested_block_scopes() {
        let mut checker = TypeChecker::new();

        // Global scope
        checker.environment.add_variable(
            "global".to_string(),
            VariableInfo {
                var_type: Type::I32,
                mutable: false,
                initialized: true,
            },
        );

        // Level 1 scope
        checker.environment.push_scope();
        checker.environment.add_variable(
            "level1".to_string(),
            VariableInfo {
                var_type: Type::I64,
                mutable: false,
                initialized: true,
            },
        );

        // Level 2 scope
        checker.environment.push_scope();
        checker.environment.add_variable(
            "level2".to_string(),
            VariableInfo {
                var_type: Type::Bool,
                mutable: false,
                initialized: true,
            },
        );

        // All variables should be accessible from deepest scope
        assert!(checker.environment.get_variable("global").is_some());
        assert!(checker.environment.get_variable("level1").is_some());
        assert!(checker.environment.get_variable("level2").is_some());

        // Pop level 2
        checker.environment.pop_scope();
        assert!(checker.environment.get_variable("global").is_some());
        assert!(checker.environment.get_variable("level1").is_some());
        assert!(checker.environment.get_variable("level2").is_none());

        // Pop level 1
        checker.environment.pop_scope();
        assert!(checker.environment.get_variable("global").is_some());
        assert!(checker.environment.get_variable("level1").is_none());
        assert!(checker.environment.get_variable("level2").is_none());
    }

    #[test]
    fn test_variable_shadowing() {
        let mut checker = TypeChecker::new();

        // Add variable 'x' in outer scope
        checker.environment.add_variable(
            "x".to_string(),
            VariableInfo {
                var_type: Type::I32,
                mutable: false,
                initialized: true,
            },
        );

        // Verify outer variable
        assert_eq!(
            checker.environment.get_variable("x").unwrap().var_type,
            Type::I32
        );

        // Enter inner scope and shadow 'x'
        checker.environment.push_scope();
        checker.environment.add_variable(
            "x".to_string(),
            VariableInfo {
                var_type: Type::I64,
                mutable: true,
                initialized: true,
            },
        );

        // Should see inner variable (shadowing)
        let var_info = checker.environment.get_variable("x").unwrap();
        assert_eq!(var_info.var_type, Type::I64);
        assert!(var_info.mutable);

        // Exit inner scope
        checker.environment.pop_scope();

        // Should see outer variable again
        let var_info = checker.environment.get_variable("x").unwrap();
        assert_eq!(var_info.var_type, Type::I32);
        assert!(!var_info.mutable);
    }

    #[test]
    fn test_block_with_variable_definitions() {
        use parser;

        let mut checker = TypeChecker::new();

        // Parse actual source code with a block
        let source = "fn test() -> i32 { let x: i32 = 42; x }";
        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let func_def = &program.functions[0];
        let block = &func_def.body;

        // Variable x should not exist before block
        assert!(checker.environment.get_variable("x").is_none());

        // This will fail because identifier checking is not implemented yet
        // But it should succeed for the variable definition part
        let _result = checker.check_block(block);

        // Variable x should not exist after block (scope was popped)
        assert!(checker.environment.get_variable("x").is_none());
    }

    #[test]
    fn test_integration_simple_function() {
        use parser;

        let mut checker = TypeChecker::new();

        let source = r#"
            fn add(a: i32, b: i32) -> i32 {
                a + b
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();

        // Check the structure - this should now work with identifier expressions implemented
        for function in &program.functions {
            let result = checker.check_function_definition(function);
            // This should succeed now that identifier expressions are implemented
            assert!(result.is_ok());
        }

        // Verify function was registered
        let func_info = checker.environment.get_function("add").unwrap();
        assert_eq!(func_info.parameters, vec![Type::I32, Type::I32]);
        assert_eq!(func_info.return_type, Type::I32);
    }

    #[test]
    fn test_integration_variable_scoping() {
        use parser;

        let mut checker = TypeChecker::new();

        let source = r#"
            fn test() -> i32 {
                let outer: i32 = 10;
                let inner: i32 = 20;
                inner
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];

        // This should now work with identifier expressions implemented
        let result = checker.check_function_definition(function);
        assert!(result.is_ok()); // Should succeed now
    }

    #[test]
    fn test_integration_type_error() {
        use parser;

        let mut checker = TypeChecker::new();

        let source = r#"
            fn bad_function() -> i32 {
                let x: i64 = 42;
                x
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];

        let result = checker.check_function_definition(function);
        assert!(result.is_err()); // Should fail due to type mismatch (i64 vs i32) or identifier issue
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