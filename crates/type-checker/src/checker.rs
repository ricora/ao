use crate::env::{FunctionInfo, TypeEnvironment, VariableInfo};
use crate::error::TypeCheckError;
use ast::{Type, TypeKind};

// Type aliases for typed AST where all nodes have concrete types (not Option<Type>)
// These represent the result of successful type checking where every expression
// has been assigned a definite type.
pub type TypedExpression<'a> = ast::Expression<'a, Type>;
pub type TypedStatement<'a> = ast::Statement<'a, Type>;
pub type TypedBlock<'a> = ast::Block<'a, Type>;
pub type TypedFunctionDefinition<'a> = ast::FunctionDefinition<'a, Type>;
pub type TypedProgram<'a> = ast::Program<'a, Type>;

pub struct TypeChecker {
    pub environment: TypeEnvironment,
}

impl TypeChecker {
    /// Helper function to create a Type with the given kind and location
    fn create_type(kind: TypeKind, location: &ast::Location) -> Type {
        Type {
            kind,
            location: location.clone(),
        }
    }

    pub fn new() -> Self {
        let mut environment = TypeEnvironment::new();

        // Initialize the environment with built-in types and functions
        environment.add_function(
            "print_char".to_string(),
            FunctionInfo {
                parameters: vec![TypeKind::I32],
                return_type: TypeKind::I32,
            },
        );
        environment.add_function(
            "print_int".to_string(),
            FunctionInfo {
                parameters: vec![TypeKind::I32],
                return_type: TypeKind::I32,
            },
        );

        Self { environment }
    }

    pub fn check_integer_literal<'a>(
        &self,
        literal: &ast::IntegerLiteral<'a>,
    ) -> Result<(TypeKind, TypedExpression<'a>), TypeCheckError> {
        // Integer literals default to i32 according to spec
        let type_kind = TypeKind::I32;
        let typed_literal = ast::Expression::IntegerLiteral(ast::IntegerLiteral {
            value: literal.value,
            r#type: Self::create_type(type_kind.clone(), &literal.location),
            location: literal.location.clone(),
        });
        Ok((type_kind, typed_literal))
    }

    pub fn check_boolean_literal<'a>(
        &self,
        literal: &ast::BooleanLiteral,
    ) -> Result<(TypeKind, TypedExpression<'a>), TypeCheckError> {
        // Boolean literals always have type Bool
        let type_kind = TypeKind::Bool;
        let typed_literal = ast::Expression::BooleanLiteral(ast::BooleanLiteral {
            value: literal.value,
            r#type: Self::create_type(type_kind.clone(), &literal.location),
            location: literal.location.clone(),
        });
        Ok((type_kind, typed_literal))
    }

    pub fn check_identifier_expression<'a>(
        &self,
        identifier: &ast::IdentifierExpression<'a>,
    ) -> Result<(TypeKind, TypedExpression<'a>), TypeCheckError> {
        match self.environment.get_variable(identifier.identifier.name) {
            Some(var_info) => {
                if !var_info.initialized {
                    Err(TypeCheckError::UninitializedVariable {
                        name: identifier.identifier.name.to_string(),
                        location: identifier.location.clone(),
                    })
                } else {
                    let type_kind = var_info.var_type.clone();
                    let typed_identifier =
                        ast::Expression::IdentifierExpression(ast::IdentifierExpression {
                            identifier: identifier.identifier.clone(),
                            r#type: Self::create_type(type_kind.clone(), &identifier.location),
                            location: identifier.location.clone(),
                        });
                    Ok((type_kind, typed_identifier))
                }
            }
            None => Err(TypeCheckError::UndefinedIdentifier {
                name: identifier.identifier.name.to_string(),
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
    pub fn check_function_call<'a>(
        &mut self,
        function_call: &ast::FunctionCall<'a>,
    ) -> Result<(TypeKind, TypedExpression<'a>), TypeCheckError> {
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

        // Validate each argument type matches corresponding parameter type and collect typed arguments
        let mut typed_arguments = Vec::with_capacity(function_call.arguments.len());
        for (arg_expr, expected_type) in function_call.arguments.iter().zip(&func_info.parameters) {
            let (arg_type, typed_arg) = self.check_expression(arg_expr)?;
            if arg_type != *expected_type {
                return Err(TypeCheckError::FunctionCallArgumentMismatch {
                    location: function_call.location.clone(),
                });
            }
            typed_arguments.push(typed_arg);
        }

        // Function call is valid - return the function's return type and typed AST
        let type_kind = func_info.return_type;
        let typed_function_call = ast::Expression::FunctionCall(ast::FunctionCall {
            name: function_call.name.clone(),
            arguments: typed_arguments,
            r#type: Type {
                kind: type_kind.clone(),
                location: function_call.location.clone(),
            },
            location: function_call.location.clone(),
        });
        Ok((type_kind, typed_function_call))
    }

    /// Type checks an expression and returns both its type and a typed AST node.
    ///
    /// Returns a tuple of (TypeKind, TypedExpression) where:
    /// - TypeKind is the inferred/checked type of the expression
    /// - TypedExpression is the same expression but with all type information filled in
    pub fn check_expression<'a>(
        &mut self,
        expr: &ast::Expression<'a>,
    ) -> Result<(TypeKind, TypedExpression<'a>), TypeCheckError> {
        match expr {
            ast::Expression::IntegerLiteral(literal) => self.check_integer_literal(literal),
            ast::Expression::BooleanLiteral(boolean_literal) => {
                self.check_boolean_literal(boolean_literal)
            }
            ast::Expression::BinaryExpression(binary) => self.check_binary_expression(binary),
            ast::Expression::UnaryExpression(unary) => self.check_unary_expression(unary),
            ast::Expression::AssignmentExpression(assignment) => {
                self.check_assignment_expression(assignment)
            }
            ast::Expression::IdentifierExpression(identifier) => {
                self.check_identifier_expression(identifier)
            }
            ast::Expression::FunctionCall(function_call) => self.check_function_call(function_call),
        }
    }

    pub fn check_unary_expression<'a>(
        &mut self,
        unary: &ast::UnaryExpression<'a>,
    ) -> Result<(TypeKind, TypedExpression<'a>), TypeCheckError> {
        let (operand_type, typed_operand) = self.check_expression(&unary.operand)?;

        use ast::UnaryOperatorKind;
        let result_type = match unary.operator.operator {
            // Numeric negation: operand numeric type → same type
            UnaryOperatorKind::Negate => {
                if matches!(operand_type, TypeKind::I32 | TypeKind::I64) {
                    operand_type
                } else {
                    return Err(TypeCheckError::TypeMismatch {
                        expected: "numeric type (i32 or i64)".to_string(),
                        found: operand_type.to_string(),
                        location: unary.location.clone(),
                    });
                }
            }
            // Logical not: operand bool → bool
            UnaryOperatorKind::Not => {
                if operand_type == TypeKind::Bool {
                    TypeKind::Bool
                } else {
                    return Err(TypeCheckError::TypeMismatch {
                        expected: "bool".to_string(),
                        found: operand_type.to_string(),
                        location: unary.location.clone(),
                    });
                }
            }
        };

        let typed_unary = ast::Expression::UnaryExpression(ast::UnaryExpression {
            operator: unary.operator.clone(),
            operand: Box::new(typed_operand),
            r#type: Type {
                kind: result_type.clone(),
                location: unary.location.clone(),
            },
            location: unary.location.clone(),
        });

        Ok((result_type, typed_unary))
    }

    pub fn check_assignment_expression<'a>(
        &mut self,
        assignment: &ast::AssignmentExpression<'a>,
    ) -> Result<(TypeKind, TypedExpression<'a>), TypeCheckError> {
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
        let (value_type, typed_value) = self.check_expression(&assignment.value)?;

        // Check if the types match
        if value_type != var_info.var_type {
            return Err(TypeCheckError::TypeMismatch {
                expected: var_info.var_type.to_string(),
                found: value_type.to_string(),
                location: assignment.location.clone(),
            });
        }

        // Assignment expression returns the type of the assigned value
        let typed_assignment = ast::Expression::AssignmentExpression(ast::AssignmentExpression {
            name: assignment.name.clone(),
            value: Box::new(typed_value),
            location: assignment.location.clone(),
        });

        Ok((value_type, typed_assignment))
    }

    pub fn check_binary_expression<'a>(
        &mut self,
        binary: &ast::BinaryExpression<'a>,
    ) -> Result<(TypeKind, TypedExpression<'a>), TypeCheckError> {
        let (left_type, typed_left) = self.check_expression(&binary.left)?;
        let (right_type, typed_right) = self.check_expression(&binary.right)?;

        use ast::BinaryOperatorKind;
        let result_type = match binary.operator.operator {
            // Arithmetic operators: operands same numeric type → same type
            BinaryOperatorKind::Add
            | BinaryOperatorKind::Subtract
            | BinaryOperatorKind::Multiply
            | BinaryOperatorKind::Divide => {
                if left_type == right_type && matches!(left_type, TypeKind::I32 | TypeKind::I64) {
                    left_type
                } else {
                    return Err(TypeCheckError::TypeMismatch {
                        expected: left_type.to_string(),
                        found: right_type.to_string(),
                        location: binary.location.clone(),
                    });
                }
            }
            // Comparison operators: operands same type → bool
            BinaryOperatorKind::LessThan
            | BinaryOperatorKind::LessThanOrEqual
            | BinaryOperatorKind::GreaterThan
            | BinaryOperatorKind::GreaterThanOrEqual
            | BinaryOperatorKind::Equal
            | BinaryOperatorKind::NotEqual => {
                if left_type == right_type {
                    TypeKind::Bool
                } else {
                    return Err(TypeCheckError::TypeMismatch {
                        expected: left_type.to_string(),
                        found: right_type.to_string(),
                        location: binary.location.clone(),
                    });
                }
            }
            // Logical operators: operands bool → bool
            BinaryOperatorKind::LogicalAnd | BinaryOperatorKind::LogicalOr => {
                if left_type == TypeKind::Bool && right_type == TypeKind::Bool {
                    TypeKind::Bool
                } else {
                    return Err(TypeCheckError::TypeMismatch {
                        expected: "bool".to_string(),
                        found: if left_type != TypeKind::Bool {
                            left_type.to_string()
                        } else {
                            right_type.to_string()
                        },
                        location: binary.location.clone(),
                    });
                }
            }
        };

        let typed_binary = ast::Expression::BinaryExpression(ast::BinaryExpression {
            left: Box::new(typed_left),
            operator: binary.operator.clone(),
            right: Box::new(typed_right),
            r#type: Type {
                kind: result_type.clone(),
                location: binary.location.clone(),
            },
            location: binary.location.clone(),
        });

        Ok((result_type, typed_binary))
    }

    pub fn check_variable_definition(
        &mut self,
        var_def: &ast::VariableDefinition,
    ) -> Result<(), TypeCheckError> {
        let declared_type = match &var_def.variable_type {
            Some(type_info) => type_info.kind.clone(),
            None => {
                return Err(TypeCheckError::MissingTypeAnnotation {
                    location: var_def.location.clone(),
                });
            }
        };

        let initialized = if let Some(value_expr) = &var_def.value {
            // Check if the value expression type matches the declared type
            let (value_type, _typed_expr) = self.check_expression(value_expr)?;
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
    ) -> Result<TypeKind, TypeCheckError> {
        // Validate condition type - must be boolean
        let (condition_type, _typed_condition) = self.check_expression(&if_stmt.condition)?;
        if condition_type != TypeKind::Bool {
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
        Ok(TypeKind::Unit)
    }

    pub fn check_statement(
        &mut self,
        statement: &ast::Statement,
    ) -> Result<TypeKind, TypeCheckError> {
        match statement {
            ast::Statement::VariableDefinition(var_def) => {
                self.check_variable_definition(var_def)?;
                Ok(TypeKind::Unit)
            }
            ast::Statement::ExpressionStatement(expr_stmt) => {
                let (_expr_type, _typed_expr) = self.check_expression(&expr_stmt.expression)?;
                Ok(TypeKind::Unit)
            }
            ast::Statement::IfStatement(if_stmt) => self.check_if_statement(if_stmt),
            ast::Statement::Expression(expr) => {
                let (expr_type, _typed_expr) = self.check_expression(expr)?;
                Ok(expr_type)
            }
        }
    }

    pub fn check_block(&mut self, block: &ast::Block) -> Result<TypeKind, TypeCheckError> {
        let statements = &block.statements.statements;

        if statements.is_empty() {
            return Ok(TypeKind::Unit);
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
        let return_type = match &func_def.return_type {
            Some(type_info) => type_info.kind.clone(),
            None => {
                return Err(TypeCheckError::MissingTypeAnnotation {
                    location: func_def.location.clone(),
                });
            }
        };

        // Check for duplicate function definition
        if self.environment.get_function(func_def.name.name).is_some() {
            return Err(TypeCheckError::DuplicateDefinition {
                name: func_def.name.name.to_string(),
                location: func_def.location.clone(),
            });
        }

        // Collect parameter types
        let param_types: Vec<TypeKind> = func_def
            .parameters
            .parameters
            .iter()
            .map(|param| match &param.parameter_type {
                Some(type_info) => Ok(type_info.kind.clone()),
                None => Err(TypeCheckError::MissingTypeAnnotation {
                    location: param.location.clone(),
                }),
            })
            .collect::<Result<Vec<_>, _>>()?;

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

    pub fn check_program(&mut self, program: &ast::Program) -> Result<(), TypeCheckError> {
        // Check each function definition
        for func_def in &program.functions {
            self.check_function_definition(func_def)?;
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
            r#type: None,
        };

        let result = checker.check_integer_literal(&literal);
        assert_eq!(result.unwrap().0, TypeKind::I32);
    }

    #[test]
    fn test_check_binary_expression_arithmetic() {
        use ast::{
            BinaryExpression, BinaryOperator, BinaryOperatorKind, Expression, IntegerLiteral,
            Location,
        };

        let mut checker = TypeChecker::new();

        let left = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "1",
            location: Location {
                start: 0,
                end: 1,
                context: (),
            },
            r#type: None,
        }));

        let right = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "2",
            location: Location {
                start: 4,
                end: 5,
                context: (),
            },
            r#type: None,
        }));

        let binary_expr = BinaryExpression {
            left,
            operator: BinaryOperator {
                operator: BinaryOperatorKind::Add,
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
            r#type: None,
        };

        let result = checker.check_binary_expression(&binary_expr);
        assert_eq!(result.unwrap().0, TypeKind::I32);
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
            assert_eq!(var_info.var_type, TypeKind::I32);
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
        assert_eq!(func_info.parameters, vec![TypeKind::I32, TypeKind::I32]);
        assert_eq!(func_info.return_type, TypeKind::I32);
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
        assert_eq!(func_info.parameters, vec![TypeKind::I32, TypeKind::I32]);
        assert_eq!(func_info.return_type, TypeKind::I32);
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
            assert_eq!(result.unwrap(), TypeKind::Unit);

            // Check that variable was added to environment
            let var_info = checker.environment.get_variable("x").unwrap();
            assert_eq!(var_info.var_type, TypeKind::I32);
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
            assert_eq!(result.unwrap(), TypeKind::Unit);
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
            assert_eq!(result.unwrap(), TypeKind::I32);
        } else {
            panic!("Expected expression statement");
        }
    }

    #[test]
    fn test_check_unary_expression_logical_not() {
        use ast::{
            Expression, IntegerLiteral, Location, UnaryExpression, UnaryOperator, UnaryOperatorKind,
        };

        let mut checker = TypeChecker::new();

        // Test !42 (should fail - can't apply logical not to integer)
        let operand = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "42",
            location: Location {
                start: 1,
                end: 3,
                context: (),
            },
            r#type: None,
        }));

        let unary_expr = UnaryExpression {
            operator: UnaryOperator {
                operator: UnaryOperatorKind::Not,
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
            r#type: None,
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
            BinaryExpression, BinaryOperator, BinaryOperatorKind, Expression, IntegerLiteral,
            Location, UnaryExpression, UnaryOperator, UnaryOperatorKind,
        };

        // Create 1 == 2 (which is bool)
        let left = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "1",
            location: Location {
                start: 0,
                end: 1,
                context: (),
            },
            r#type: None,
        }));
        let right = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "2",
            location: Location {
                start: 5,
                end: 6,
                context: (),
            },
            r#type: None,
        }));
        let comparison = Box::new(Expression::BinaryExpression(BinaryExpression {
            left,
            operator: BinaryOperator {
                operator: BinaryOperatorKind::Equal,
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
            r#type: None,
        }));

        // Apply logical not to the comparison: !(1 == 2)
        let unary_expr = UnaryExpression {
            operator: UnaryOperator {
                operator: UnaryOperatorKind::Not,
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
            r#type: None,
        };

        let result = checker.check_unary_expression(&unary_expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, TypeKind::Bool);
    }

    #[test]
    fn test_check_assignment_expression_success() {
        use ast::{AssignmentExpression, Expression, Identifier, IntegerLiteral, Location};

        let mut checker = TypeChecker::new();

        // First, add a mutable variable to the environment
        checker.environment.add_variable(
            "x".to_string(),
            crate::env::VariableInfo {
                var_type: TypeKind::I32,
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
                r#type: None,
            })),
            location: Location {
                start: 0,
                end: 6,
                context: (),
            },
        };

        let result = checker.check_assignment_expression(&assignment_expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, TypeKind::I32);
    }

    #[test]
    fn test_check_assignment_expression_immutable_variable() {
        use ast::{AssignmentExpression, Expression, Identifier, IntegerLiteral, Location};

        let mut checker = TypeChecker::new();

        // Add an immutable variable to the environment
        checker.environment.add_variable(
            "x".to_string(),
            crate::env::VariableInfo {
                var_type: TypeKind::I32,
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
                r#type: None,
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
                r#type: None,
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
                var_type: TypeKind::I64,
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
                r#type: None,
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
            BinaryExpression, BinaryOperator, BinaryOperatorKind, Block, Expression, IfStatement,
            IntegerLiteral, Location, Statement, Statements,
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
            r#type: None,
        }));
        let right = Box::new(Expression::IntegerLiteral(IntegerLiteral {
            value: "1",
            location: Location {
                start: 8,
                end: 9,
                context: (),
            },
            r#type: None,
        }));
        let condition = Expression::BinaryExpression(BinaryExpression {
            left,
            operator: BinaryOperator {
                operator: BinaryOperatorKind::Equal,
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
            r#type: None,
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
        assert_eq!(result.unwrap(), TypeKind::Unit);
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

    #[test]
    fn test_check_expression_returns_typed_ast() {
        use ast::{IntegerLiteral, Location};

        let mut checker = TypeChecker::new();
        let literal = ast::Expression::IntegerLiteral(IntegerLiteral {
            value: "42",
            location: Location {
                start: 0,
                end: 2,
                context: (),
            },
            r#type: None,
        });

        // This should fail to compile because check_expression now returns (TypeKind, TypedExpression)
        let result: (TypeKind, TypedExpression) = checker.check_expression(&literal).unwrap();
        assert_eq!(result.0, TypeKind::I32);
        // The typed expression should have a concrete type instead of None
        if let ast::Expression::IntegerLiteral(typed_literal) = result.1 {
            assert_eq!(typed_literal.r#type.kind, TypeKind::I32);
        } else {
            panic!("Expected IntegerLiteral");
        }
    }

    #[test]
    fn test_check_function_definition_returns_typed_ast() {
        use parser;

        let mut checker = TypeChecker::new();

        let source = "fn add(x: i32, y: i32) -> i32 { x + y }";
        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();
        let func_def = &program.functions[0];

        // This should fail to compile because check_function_definition now returns TypedFunctionDefinition
        let result: TypedFunctionDefinition = checker.check_function_definition(func_def).unwrap();
        
        // The typed function should have all type information filled in
        assert_eq!(result.return_type.kind, TypeKind::I32);
    }

    #[test]
    fn test_check_program_returns_typed_ast() {
        use parser;

        let mut checker = TypeChecker::new();

        let source = r#"
            fn add(x: i32, y: i32) -> i32 { x + y }
            fn main() -> i32 { add(1, 2) }
        "#;
        let parse_result = parser::parse(source);
        assert!(parse_result.output().is_some());

        let program = parse_result.output().unwrap();

        // This should fail to compile because check_program now returns TypedProgram
        let result: TypedProgram = checker.check_program(&program).unwrap();
        
        // The typed program should have all functions with type information
        assert_eq!(result.functions.len(), 2);
        for func in &result.functions {
            // Each function should have concrete type information
            assert_eq!(func.return_type.kind, TypeKind::I32);
        }
    }
}
