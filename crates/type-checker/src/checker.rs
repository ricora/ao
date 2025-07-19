use crate::env::{FunctionInfo, Type, TypeEnvironment, VariableInfo};
use crate::error::TypeCheckError;

pub struct TypeChecker {
    pub environment: TypeEnvironment,
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

    pub fn check_identifier_expression(
        &self,
        identifier: &ast::Identifier,
    ) -> Result<Type, TypeCheckError> {
        match self.environment.get_variable(identifier.name) {
            Some(var_info) => {
                if !var_info.initialized {
                    Err(TypeCheckError::UninitializedVariable {
                        name: identifier.name.to_string(),
                        location: identifier.location.clone(),
                    })
                } else {
                    Ok(var_info.var_type.clone())
                }
            }
            None => Err(TypeCheckError::UndefinedIdentifier {
                name: identifier.name.to_string(),
                location: identifier.location.clone(),
            }),
        }
    }

    /// Validates a function call expression by checking:
    /// 1. The function exists in the current environment
    /// 2. The number of arguments matches the function's parameter count
    /// 3. Each argument's type matches the corresponding parameter type
    ///
    /// Returns the function's return type on success.
    pub fn check_function_call(
        &mut self,
        function_call: &ast::FunctionCall,
    ) -> Result<Type, TypeCheckError> {
        // Lookup function in environment
        let func_info = match self.environment.get_function(function_call.name.name) {
            Some(info) => info.clone(),
            None => {
                return Err(TypeCheckError::UndefinedIdentifier {
                    name: function_call.name.name.to_string(),
                    location: function_call.name.location.clone(),
                });
            }
        };

        // Validate argument count matches parameter count
        if function_call.arguments.len() != func_info.parameters.len() {
            return Err(TypeCheckError::FunctionCallArgumentMismatch {
                location: function_call.location.clone(),
            });
        }

        // Validate each argument type matches corresponding parameter type
        for (arg_expr, expected_type) in function_call.arguments.iter().zip(&func_info.parameters) {
            let arg_type = self.check_expression(arg_expr)?;
            if arg_type != *expected_type {
                return Err(TypeCheckError::FunctionCallArgumentMismatch {
                    location: function_call.location.clone(),
                });
            }
        }

        // Function call is valid - return the function's return type
        Ok(func_info.return_type)
    }

    pub fn check_expression(&mut self, expr: &ast::Expression) -> Result<Type, TypeCheckError> {
        match expr {
            ast::Expression::IntegerLiteral(literal) => self.check_integer_literal(literal),
            ast::Expression::BinaryExpression(binary) => self.check_binary_expression(binary),
            ast::Expression::UnaryExpression(unary) => self.check_unary_expression(unary),
            ast::Expression::AssignmentExpression(assignment) => {
                self.check_assignment_expression(assignment)
            }
            ast::Expression::Identifier(identifier) => self.check_identifier_expression(identifier),
            ast::Expression::FunctionCall(function_call) => self.check_function_call(function_call),
        }
    }

    pub fn check_unary_expression(
        &mut self,
        unary: &ast::UnaryExpression,
    ) -> Result<Type, TypeCheckError> {
        let operand_type = self.check_expression(&unary.operand)?;

        use ast::OperatorKind;
        match unary.operator.operator {
            // Numeric negation: operand numeric type → same type
            OperatorKind::Subtract => {
                if matches!(operand_type, Type::I32 | Type::I64) {
                    Ok(operand_type)
                } else {
                    Err(TypeCheckError::TypeMismatch {
                        expected: "numeric type (i32 or i64)".to_string(),
                        found: operand_type.to_string(),
                        location: unary.location.clone(),
                    })
                }
            }
            // Logical not: operand bool → bool
            OperatorKind::LogicalNot => {
                if operand_type == Type::Bool {
                    Ok(Type::Bool)
                } else {
                    Err(TypeCheckError::TypeMismatch {
                        expected: "bool".to_string(),
                        found: operand_type.to_string(),
                        location: unary.location.clone(),
                    })
                }
            }
            // Other operators are not valid for unary expressions
            _ => Err(TypeCheckError::InvalidOperator {
                operator: unary.operator.operator.to_string(),
                location: unary.operator.location.clone(),
            }),
        }
    }

    pub fn check_assignment_expression(
        &mut self,
        assignment: &ast::AssignmentExpression,
    ) -> Result<Type, TypeCheckError> {
        // Check if the variable exists
        let var_info = match self.environment.get_variable(assignment.name.name) {
            Some(info) => info.clone(),
            None => {
                return Err(TypeCheckError::UndefinedIdentifier {
                    name: assignment.name.name.to_string(),
                    location: assignment.name.location.clone(),
                });
            }
        };

        // Check if the variable is mutable
        if !var_info.mutable {
            return Err(TypeCheckError::AssignmentToImmutable {
                name: assignment.name.name.to_string(),
                location: assignment.name.location.clone(),
            });
        }

        // Check the type of the value being assigned
        let value_type = self.check_expression(&assignment.value)?;

        // Check if the types match
        if value_type != var_info.var_type {
            return Err(TypeCheckError::TypeMismatch {
                expected: var_info.var_type.to_string(),
                found: value_type.to_string(),
                location: assignment.location.clone(),
            });
        }

        // Assignment expression returns the type of the assigned value
        Ok(value_type)
    }

    pub fn check_binary_expression(
        &mut self,
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

    pub fn check_if_statement(
        &mut self,
        if_stmt: &ast::IfStatement,
    ) -> Result<Type, TypeCheckError> {
        // Validate condition type - must be boolean
        let condition_type = self.check_expression(&if_stmt.condition)?;
        if condition_type != Type::Bool {
            return Err(TypeCheckError::TypeMismatch {
                expected: "bool".to_string(),
                found: condition_type.to_string(),
                location: if_stmt.condition.location().clone(),
            });
        }

        // Check then branch - this creates a new scope
        self.check_block(&if_stmt.then_block)?;

        // Check else branch if present - this also creates a new scope
        if let Some(else_block) = &if_stmt.else_block {
            self.check_block(else_block)?;
        }

        // If statements always evaluate to Unit type
        Ok(Type::Unit)
    }

    pub fn check_statement(&mut self, statement: &ast::Statement) -> Result<Type, TypeCheckError> {
        match statement {
            ast::Statement::VariableDefinition(var_def) => {
                self.check_variable_definition(var_def)?;
                Ok(Type::Unit)
            }
            ast::Statement::ExpressionStatement(expr_stmt) => {
                self.check_expression(&expr_stmt.expression)?;
                Ok(Type::Unit)
            }
            ast::Statement::IfStatement(if_stmt) => self.check_if_statement(if_stmt),
            ast::Statement::Expression(expr) => self.check_expression(expr),
        }
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
            if let ast::Statement::Expression(expr) = statement {
                // Expression statements are only allowed as the last statement in a block
                self.environment.pop_scope();
                return Err(TypeCheckError::ExpressionMustBeLastInBlock {
                    location: expr.location().clone(),
                });
            }

            if let Err(e) = self.check_statement(statement) {
                self.environment.pop_scope();
                return Err(e);
            }
        }

        // The type of the block is the type of the last statement
        let result = self.check_statement(statements.last().unwrap());

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
        error.format(source_id, source)
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

        let mut checker = TypeChecker::new();

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
            let result = checker.check_variable_definition(var_def);
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
    fn test_check_statement_variable_definition() {
        use parser;

        let mut checker = TypeChecker::new();

        let source = "fn main() -> i32 { let x: i32 = 42; x }";
        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];
        let statements = &function.body.statements.statements;

        // Test variable definition statement
        if let ast::Statement::VariableDefinition(_) = &statements[0] {
            let result = checker.check_statement(&statements[0]);
            assert!(result.is_ok());
            assert_eq!(result.unwrap(), Type::Unit);

            // Check that variable was added to environment
            let var_info = checker.environment.get_variable("x").unwrap();
            assert_eq!(var_info.var_type, Type::I32);
        } else {
            panic!("Expected variable definition statement");
        }
    }

    #[test]
    fn test_check_statement_expression_statement() {
        use parser;

        let mut checker = TypeChecker::new();

        let source = "fn main() -> i32 { let x: i32 = 42; x; }";
        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];
        let statements = &function.body.statements.statements;

        // Add the variable first
        if let ast::Statement::VariableDefinition(var_def) = &statements[0] {
            checker.check_variable_definition(var_def).unwrap();
        }

        // Test expression statement (x;)
        if let ast::Statement::ExpressionStatement(_) = &statements[1] {
            let result = checker.check_statement(&statements[1]);
            assert!(result.is_ok());
            assert_eq!(result.unwrap(), Type::Unit);
        } else {
            panic!("Expected expression statement");
        }
    }

    #[test]
    fn test_check_statement_expression() {
        use parser;

        let mut checker = TypeChecker::new();

        let source = "fn main() -> i32 { let x: i32 = 42; x }";
        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];
        let statements = &function.body.statements.statements;

        // Add the variable first
        if let ast::Statement::VariableDefinition(var_def) = &statements[0] {
            checker.check_variable_definition(var_def).unwrap();
        }

        // Test expression statement (final x)
        if let ast::Statement::Expression(_) = &statements[1] {
            let result = checker.check_statement(&statements[1]);
            assert!(result.is_ok());
            assert_eq!(result.unwrap(), Type::I32);
        } else {
            panic!("Expected expression statement");
        }
    }

    #[test]
    fn test_check_unary_expression_logical_not() {
        use ast::{Expression, IntegerLiteral, Location, Operator, OperatorKind, UnaryExpression};

        let mut checker = TypeChecker::new();

        // Test !42 (should fail - can't apply logical not to integer)
        let operand = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "42",
            location: Location {
                start: 1,
                end: 3,
                context: (),
            },
        }));

        let unary_expr = UnaryExpression {
            operator: Operator {
                operator: OperatorKind::LogicalNot,
                location: Location {
                    start: 0,
                    end: 1,
                    context: (),
                },
            },
            operand,
            location: Location {
                start: 0,
                end: 3,
                context: (),
            },
        };

        let result = checker.check_unary_expression(&unary_expr);
        assert!(result.is_err());
    }

    #[test]
    fn test_check_unary_expression_numeric_negation() {
        use parser;

        let mut checker = TypeChecker::new();

        // Test -42 (should succeed and return i32)
        let source = r#"
            fn test() -> i32 {
                -42
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(
            parse_result.output().is_some(),
            "Parser should support numeric negation"
        );

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];

        let result = checker.check_function_definition(function);
        assert!(result.is_ok()); // Should succeed because -42 is valid i32
    }

    #[test]
    fn test_check_unary_expression_logical_not_with_bool() {
        let mut checker = TypeChecker::new();

        // Create a manual test with comparison that returns bool
        use ast::{
            BinaryExpression, Expression, IntegerLiteral, Location, Operator, OperatorKind,
            UnaryExpression,
        };

        // Create 1 == 2 (which is bool)
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
                start: 5,
                end: 6,
                context: (),
            },
        }));
        let comparison = Box::new(Expression::BinaryExpression(BinaryExpression {
            left,
            operator: Operator {
                operator: OperatorKind::Equal,
                location: Location {
                    start: 2,
                    end: 4,
                    context: (),
                },
            },
            right,
            location: Location {
                start: 0,
                end: 6,
                context: (),
            },
        }));

        // Apply logical not to the comparison: !(1 == 2)
        let unary_expr = UnaryExpression {
            operator: Operator {
                operator: OperatorKind::LogicalNot,
                location: Location {
                    start: 0,
                    end: 1,
                    context: (),
                },
            },
            operand: comparison,
            location: Location {
                start: 0,
                end: 7,
                context: (),
            },
        };

        let result = checker.check_unary_expression(&unary_expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Type::Bool);
    }

    #[test]
    fn test_check_assignment_expression_success() {
        use ast::{AssignmentExpression, Expression, Identifier, IntegerLiteral, Location};

        let mut checker = TypeChecker::new();

        // First, add a mutable variable to the environment
        checker.environment.add_variable(
            "x".to_string(),
            crate::env::VariableInfo {
                var_type: Type::I32,
                mutable: true,
                initialized: true,
            },
        );

        // Test x = 42 (should succeed)
        let assignment_expr = AssignmentExpression {
            name: Identifier {
                name: "x",
                location: Location {
                    start: 0,
                    end: 1,
                    context: (),
                },
            },
            value: Box::new(Expression::IntegerLiteral(IntegerLiteral {
                value: "42",
                location: Location {
                    start: 4,
                    end: 6,
                    context: (),
                },
            })),
            location: Location {
                start: 0,
                end: 6,
                context: (),
            },
        };

        let result = checker.check_assignment_expression(&assignment_expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Type::I32);
    }

    #[test]
    fn test_check_assignment_expression_immutable_variable() {
        use ast::{AssignmentExpression, Expression, Identifier, IntegerLiteral, Location};

        let mut checker = TypeChecker::new();

        // Add an immutable variable to the environment
        checker.environment.add_variable(
            "x".to_string(),
            crate::env::VariableInfo {
                var_type: Type::I32,
                mutable: false,
                initialized: true,
            },
        );

        // Test x = 42 (should fail - immutable variable)
        let assignment_expr = AssignmentExpression {
            name: Identifier {
                name: "x",
                location: Location {
                    start: 0,
                    end: 1,
                    context: (),
                },
            },
            value: Box::new(Expression::IntegerLiteral(IntegerLiteral {
                value: "42",
                location: Location {
                    start: 4,
                    end: 6,
                    context: (),
                },
            })),
            location: Location {
                start: 0,
                end: 6,
                context: (),
            },
        };

        let result = checker.check_assignment_expression(&assignment_expr);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            TypeCheckError::AssignmentToImmutable { .. }
        ));
    }

    #[test]
    fn test_check_assignment_expression_undefined_variable() {
        use ast::{AssignmentExpression, Expression, Identifier, IntegerLiteral, Location};

        let mut checker = TypeChecker::new();

        // Test y = 42 (should fail - undefined variable)
        let assignment_expr = AssignmentExpression {
            name: Identifier {
                name: "y",
                location: Location {
                    start: 0,
                    end: 1,
                    context: (),
                },
            },
            value: Box::new(Expression::IntegerLiteral(IntegerLiteral {
                value: "42",
                location: Location {
                    start: 4,
                    end: 6,
                    context: (),
                },
            })),
            location: Location {
                start: 0,
                end: 6,
                context: (),
            },
        };

        let result = checker.check_assignment_expression(&assignment_expr);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            TypeCheckError::UndefinedIdentifier { .. }
        ));
    }

    #[test]
    fn test_check_assignment_expression_type_mismatch() {
        use ast::{AssignmentExpression, Expression, Identifier, IntegerLiteral, Location};

        let mut checker = TypeChecker::new();

        // Add a mutable i64 variable to the environment
        checker.environment.add_variable(
            "x".to_string(),
            crate::env::VariableInfo {
                var_type: Type::I64,
                mutable: true,
                initialized: true,
            },
        );

        // Test x = 42 (should fail - type mismatch: i64 vs i32)
        let assignment_expr = AssignmentExpression {
            name: Identifier {
                name: "x",
                location: Location {
                    start: 0,
                    end: 1,
                    context: (),
                },
            },
            value: Box::new(Expression::IntegerLiteral(IntegerLiteral {
                value: "42",
                location: Location {
                    start: 4,
                    end: 6,
                    context: (),
                },
            })),
            location: Location {
                start: 0,
                end: 6,
                context: (),
            },
        };

        let result = checker.check_assignment_expression(&assignment_expr);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            TypeCheckError::TypeMismatch { .. }
        ));
    }

    #[test]
    fn test_check_if_statement_valid_condition() {
        use parser;

        let mut checker = TypeChecker::new();

        // Test if statement with boolean condition (using comparison that returns bool)
        let source = r#"
            fn test() -> i32 {
                if 1 == 1 {
                    let x: i32 = 1;
                }
                42
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];

        let result = checker.check_function_definition(function);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_if_statement_with_else() {
        use parser;

        let mut checker = TypeChecker::new();

        // Test if-else statement with boolean condition (using comparison that returns bool)
        let source = r#"
            fn test() -> i32 {
                if 2 > 1 {
                    let x: i32 = 1;
                } else {
                    let y: i32 = 2;
                }
                42
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];

        let result = checker.check_function_definition(function);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_if_statement_invalid_condition() {
        use parser;

        let mut checker = TypeChecker::new();

        // Test if statement with non-boolean condition (should fail)
        let source = r#"
            fn test() -> i32 {
                if 42 {
                    let x: i32 = 1;
                }
                42
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];

        let result = checker.check_function_definition(function);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            TypeCheckError::TypeMismatch { .. }
        ));
    }

    #[test]
    fn test_check_if_statement_returns_unit() {
        use ast::{
            BinaryExpression, Block, Expression, IfStatement, IntegerLiteral, Location, Operator,
            OperatorKind, Statement, Statements,
        };

        let mut checker = TypeChecker::new();

        // Create a manual if statement with a boolean condition (1 == 1)
        let left = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "1",
            location: Location {
                start: 3,
                end: 4,
                context: (),
            },
        }));
        let right = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "1",
            location: Location {
                start: 8,
                end: 9,
                context: (),
            },
        }));
        let condition = Expression::BinaryExpression(BinaryExpression {
            left,
            operator: Operator {
                operator: OperatorKind::Equal,
                location: Location {
                    start: 5,
                    end: 7,
                    context: (),
                },
            },
            right,
            location: Location {
                start: 3,
                end: 9,
                context: (),
            },
        });

        let if_stmt = IfStatement {
            condition,
            then_block: Block {
                statements: Statements {
                    statements: vec![],
                    location: Location {
                        start: 11,
                        end: 13,
                        context: (),
                    },
                },
                location: Location {
                    start: 11,
                    end: 13,
                    context: (),
                },
            },
            else_block: None,
            location: Location {
                start: 0,
                end: 13,
                context: (),
            },
        };

        // Test that check_if_statement returns Unit type
        let result = checker.check_statement(&Statement::IfStatement(if_stmt));
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Type::Unit);
    }

    #[test]
    fn test_check_if_statement_scoping_variables() {
        use parser;

        let mut checker = TypeChecker::new();

        // Test: if statement variables should not leak to outer scope
        let source = r#"
            fn test() -> i32 {
                if 1 == 1 {
                    let x: i32 = 42;
                }
                x
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let function = &program.functions[0];

        // This should fail because variable x is not accessible outside the if block
        let result = checker.check_function_definition(function);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            TypeCheckError::UndefinedIdentifier { .. }
        ));
    }

    #[test]
    fn test_check_function_call_basic() {
        use parser;

        let mut checker = TypeChecker::new();

        // First define a function to call
        let source = r#"
            fn add(x: i32, y: i32) -> i32 { x + y }
            fn main() -> i32 { add(1, 2) }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();

        // Register the add function first
        let add_func = &program.functions[0];
        checker.check_function_definition(add_func).unwrap();

        // Now check the main function with function call
        let main_func = &program.functions[1];
        let result = checker.check_function_definition(main_func);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_function_call_wrong_argument_count() {
        use parser;

        let mut checker = TypeChecker::new();

        // Define function that takes 2 parameters but call with 1
        let source = r#"
            fn add(x: i32, y: i32) -> i32 { x + y }
            fn main() -> i32 { add(1) }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();

        // Register the add function first
        let add_func = &program.functions[0];
        checker.check_function_definition(add_func).unwrap();

        // This should fail due to wrong argument count
        let main_func = &program.functions[1];
        let result = checker.check_function_definition(main_func);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            TypeCheckError::FunctionCallArgumentMismatch { .. }
        ));
    }

    #[test]
    fn test_check_function_call_wrong_argument_types() {
        use parser;

        let mut checker = TypeChecker::new();

        // Define function that takes i32 but call with wrong type
        let source = r#"
            fn square(x: i64) -> i64 { x }
            fn main() -> i64 { square(42) }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();

        // Register the square function first
        let square_func = &program.functions[0];
        checker.check_function_definition(square_func).unwrap();

        // This should fail due to wrong argument type (42 is i32, but function expects i64)
        let main_func = &program.functions[1];
        let result = checker.check_function_definition(main_func);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            TypeCheckError::FunctionCallArgumentMismatch { .. }
        ));
    }

    #[test]
    fn test_check_function_call_undefined_function() {
        use parser;

        let mut checker = TypeChecker::new();

        // Call undefined function
        let source = r#"
            fn main() -> i32 { undefined_function(1, 2) }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();

        // This should fail due to undefined function
        let main_func = &program.functions[0];
        let result = checker.check_function_definition(main_func);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            TypeCheckError::UndefinedIdentifier { .. }
        ));
    }

    #[test]
    fn test_check_function_call_return_type() {
        use parser;

        let mut checker = TypeChecker::new();

        // Test that function call returns correct type
        let source = r#"
            fn get_bool() -> i32 { 1 }
            fn main() -> i32 { 
                let x: i32 = get_bool();
                x
            }
        "#;

        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();

        // Register the get_bool function first
        let get_bool_func = &program.functions[0];
        checker.check_function_definition(get_bool_func).unwrap();

        // This should succeed because function returns i32 which matches variable type
        let main_func = &program.functions[1];
        let result = checker.check_function_definition(main_func);
        assert!(result.is_ok());
    }
}
