use crate::env::{Type, TypeEnvironment, VariableInfo, FunctionInfo};
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

    pub fn check_expression(&self, expr: &ast::Expression) -> Result<Type, TypeCheckError> {
        match expr {
            ast::Expression::IntegerLiteral(literal) => self.check_integer_literal(literal),
            ast::Expression::BinaryExpression(binary) => self.check_binary_expression(binary),
            ast::Expression::UnaryExpression(_) => todo!("Unary expressions not implemented"),
            ast::Expression::AssignmentExpression(_) => {
                todo!("Assignment expressions not implemented")
            }
            ast::Expression::Identifier(identifier) => self.check_identifier_expression(identifier),
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
        error.format(source_id, source)
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}