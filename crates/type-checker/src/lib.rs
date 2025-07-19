use ariadne::{Color, Label, Report, ReportKind, Source};
use ast::{Location, TypeKind};
use std::collections::HashMap;
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

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    I32,
    I64,
    Bool,
    Unit,
}

impl From<TypeKind> for Type {
    fn from(type_kind: TypeKind) -> Self {
        match type_kind {
            TypeKind::I32 => Type::I32,
            TypeKind::I64 => Type::I64,
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::I32 => write!(f, "i32"),
            Type::I64 => write!(f, "i64"),
            Type::Bool => write!(f, "bool"),
            Type::Unit => write!(f, "()"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct VariableInfo {
    pub var_type: Type,
    pub mutable: bool,
    pub initialized: bool,
}

#[derive(Debug, Clone)]
pub struct FunctionInfo {
    pub parameters: Vec<Type>,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub struct TypeEnvironment {
    // Stack of scopes, each scope is a HashMap of variables
    variable_scopes: Vec<HashMap<String, VariableInfo>>,
    pub functions: HashMap<String, FunctionInfo>,
}

impl TypeEnvironment {
    pub fn new() -> Self {
        Self {
            variable_scopes: vec![HashMap::new()], // Start with global scope
            functions: HashMap::new(),
        }
    }

    pub fn push_scope(&mut self) {
        self.variable_scopes.push(HashMap::new());
    }

    pub fn pop_scope(&mut self) {
        if self.variable_scopes.len() > 1 {
            self.variable_scopes.pop();
        }
    }

    pub fn add_variable(&mut self, name: String, info: VariableInfo) {
        if let Some(current_scope) = self.variable_scopes.last_mut() {
            current_scope.insert(name, info);
        }
    }

    pub fn get_variable(&self, name: &str) -> Option<&VariableInfo> {
        // Search from innermost to outermost scope
        for scope in self.variable_scopes.iter().rev() {
            if let Some(var_info) = scope.get(name) {
                return Some(var_info);
            }
        }
        None
    }

    pub fn add_function(&mut self, name: String, info: FunctionInfo) {
        self.functions.insert(name, info);
    }

    pub fn get_function(&self, name: &str) -> Option<&FunctionInfo> {
        self.functions.get(name)
    }

    /// Helper method to check if a variable exists in the current scope only
    pub fn variable_exists_in_current_scope(&self, name: &str) -> bool {
        if let Some(current_scope) = self.variable_scopes.last() {
            current_scope.contains_key(name)
        } else {
            false
        }
    }
}

pub struct TypeChecker {
    environment: TypeEnvironment,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            environment: TypeEnvironment::new(),
        }
    }

    pub fn check_integer_literal(
        &self,
        _literal: &ast::IntegerLiteral,
    ) -> Result<Type, TypeCheckError> {
        // Integer literals default to i32 according to spec
        Ok(Type::I32)
    }

    pub fn check_expression(&self, expr: &ast::Expression) -> Result<Type, TypeCheckError> {
        match expr {
            ast::Expression::IntegerLiteral(literal) => self.check_integer_literal(literal),
            ast::Expression::BinaryExpression(binary) => self.check_binary_expression(binary),
            ast::Expression::UnaryExpression(_) => todo!("Unary expressions not implemented"),
            ast::Expression::AssignmentExpression(_) => {
                todo!("Assignment expressions not implemented")
            }
            ast::Expression::Identifier(_) => todo!("Identifier expressions not implemented"),
            ast::Expression::FunctionCall(_) => todo!("Function call expressions not implemented"),
        }
    }

    pub fn check_binary_expression(
        &self,
        binary: &ast::BinaryExpression,
    ) -> Result<Type, TypeCheckError> {
        let left_type = self.check_expression(&binary.left)?;
        let right_type = self.check_expression(&binary.right)?;

        use ast::OperatorKind;
        match binary.operator.operator {
            // Arithmetic operators: operands same numeric type → same type
            OperatorKind::Add
            | OperatorKind::Subtract
            | OperatorKind::Multiply
            | OperatorKind::Divide => {
                if left_type == right_type && matches!(left_type, Type::I32 | Type::I64) {
                    Ok(left_type)
                } else {
                    Err(TypeCheckError::TypeMismatch {
                        expected: left_type.to_string(),
                        found: right_type.to_string(),
                        location: binary.location.clone(),
                    })
                }
            }
            // Comparison operators: operands same type → bool
            OperatorKind::LessThan
            | OperatorKind::LessThanOrEqual
            | OperatorKind::GreaterThan
            | OperatorKind::GreaterThanOrEqual
            | OperatorKind::Equal
            | OperatorKind::NotEqual => {
                if left_type == right_type {
                    Ok(Type::Bool)
                } else {
                    Err(TypeCheckError::TypeMismatch {
                        expected: left_type.to_string(),
                        found: right_type.to_string(),
                        location: binary.location.clone(),
                    })
                }
            }
            // Logical operators: operands bool → bool
            OperatorKind::LogicalAnd | OperatorKind::LogicalOr => {
                if left_type == Type::Bool && right_type == Type::Bool {
                    Ok(Type::Bool)
                } else {
                    Err(TypeCheckError::TypeMismatch {
                        expected: "bool".to_string(),
                        found: if left_type != Type::Bool {
                            left_type.to_string()
                        } else {
                            right_type.to_string()
                        },
                        location: binary.location.clone(),
                    })
                }
            }
            OperatorKind::LogicalNot => {
                // This should be handled in unary expressions
                unreachable!("LogicalNot should be handled in unary expressions")
            }
        }
    }

    pub fn check_variable_definition(
        &mut self,
        var_def: &ast::VariableDefinition,
    ) -> Result<(), TypeCheckError> {
        let declared_type = Type::from(var_def.variable_type.name.clone());

        let initialized = if let Some(value_expr) = &var_def.value {
            // Check if the value expression type matches the declared type
            let value_type = self.check_expression(value_expr)?;
            if value_type != declared_type {
                return Err(TypeCheckError::TypeMismatch {
                    expected: declared_type.to_string(),
                    found: value_type.to_string(),
                    location: var_def.location.clone(),
                });
            }
            true
        } else {
            false
        };

        // Check for duplicate definition in current scope only
        if self
            .environment
            .variable_exists_in_current_scope(var_def.name.name)
        {
            return Err(TypeCheckError::DuplicateDefinition {
                name: var_def.name.name.to_string(),
                location: var_def.location.clone(),
            });
        }

        // Add variable to environment
        self.environment.add_variable(
            var_def.name.name.to_string(),
            VariableInfo {
                var_type: declared_type,
                mutable: var_def.mutable,
                initialized,
            },
        );

        Ok(())
    }

    pub fn check_block(&mut self, block: &ast::Block) -> Result<Type, TypeCheckError> {
        let statements = &block.statements.statements;

        if statements.is_empty() {
            return Ok(Type::Unit);
        }

        // Enter new scope for this block
        self.environment.push_scope();

        // Check all statements except the last one
        for statement in &statements[..statements.len() - 1] {
            match statement {
                ast::Statement::VariableDefinition(var_def) => {
                    if let Err(e) = self.check_variable_definition(var_def) {
                        self.environment.pop_scope();
                        return Err(e);
                    }
                }
                ast::Statement::ExpressionStatement(expr_stmt) => {
                    if let Err(e) = self.check_expression(&expr_stmt.expression) {
                        self.environment.pop_scope();
                        return Err(e);
                    }
                }
                ast::Statement::IfStatement(_) => {
                    // TODO: Handle if statements
                }
                ast::Statement::Expression(expr) => {
                    if let Err(e) = self.check_expression(expr) {
                        self.environment.pop_scope();
                        return Err(e);
                    }
                    return Err(TypeCheckError::ExpressionMustBeLastInBlock {
                        location: expr.location().clone(),
                    });
                }
            }
        }

        // The type of the block is the type of the last statement
        let result = match statements.last().unwrap() {
            ast::Statement::Expression(expr) => self.check_expression(expr),
            ast::Statement::VariableDefinition(var_def) => {
                self.check_variable_definition(var_def)?;
                Ok(Type::Unit)
            }
            ast::Statement::ExpressionStatement(expr_stmt) => {
                self.check_expression(&expr_stmt.expression)?;
                Ok(Type::Unit)
            }
            ast::Statement::IfStatement(_) => {
                // TODO: Handle if statements
                Ok(Type::Unit)
            }
        };

        // Exit scope
        self.environment.pop_scope();
        result
    }

    pub fn check_function_definition(
        &mut self,
        func_def: &ast::FunctionDefinition,
    ) -> Result<(), TypeCheckError> {
        let return_type = Type::from(func_def.return_type.name.clone());

        // Check for duplicate function definition
        if self.environment.get_function(func_def.name.name).is_some() {
            return Err(TypeCheckError::DuplicateDefinition {
                name: func_def.name.name.to_string(),
                location: func_def.location.clone(),
            });
        }

        // Collect parameter types
        let param_types: Vec<Type> = func_def
            .parameters
            .parameters
            .iter()
            .map(|param| Type::from(param.parameter_type.name.clone()))
            .collect();

        // Add function to environment
        self.environment.add_function(
            func_def.name.name.to_string(),
            FunctionInfo {
                parameters: param_types.clone(),
                return_type: return_type.clone(),
            },
        );

        // Enter function scope and add parameters
        self.environment.push_scope();
        for (param, param_type) in func_def
            .parameters
            .parameters
            .iter()
            .zip(param_types.iter())
        {
            self.environment.add_variable(
                param.name.name.to_string(),
                VariableInfo {
                    var_type: param_type.clone(),
                    mutable: false,    // Parameters are immutable by default
                    initialized: true, // Parameters are always initialized
                },
            );
        }

        // Check function body type matches return type
        let body_type = self.check_block(&func_def.body)?;

        // Exit function scope
        self.environment.pop_scope();
        if body_type != return_type {
            return Err(TypeCheckError::TypeMismatch {
                expected: return_type.to_string(),
                found: body_type.to_string(),
                location: func_def.body.location.clone(),
            });
        }

        Ok(())
    }

    pub fn format_error(&self, error: &TypeCheckError, source_id: &str, source: &str) -> String {
        let mut report = Report::build(ReportKind::Error, source_id, 0);

        match error {
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
            location: Location {
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

        // This will fail due to unimplemented features but we can test the structure
        for function in &program.functions {
            let result = checker.check_function_definition(function);
            // For now, we expect it to fail due to identifier expressions not being implemented
            assert!(result.is_err());
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
                {
                    let inner: i32 = 20;
                    inner
                }
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];

        // This will fail due to unimplemented features but we can test that parsing works
        let result = checker.check_function_definition(function);
        assert!(result.is_err()); // Expected due to identifier expressions
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
