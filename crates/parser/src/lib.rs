mod token;

use chumsky::{
    input::{MapExtra, ValueInput},
    prelude::*,
};
use logos::Logos;
use token::Token;

pub fn parser<'a, I>() -> impl Parser<'a, I, ast::Program<'a>, extra::Err<Rich<'a, Token<'a>>>>
where
    I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>,
{
    type E<'a> = extra::Err<Rich<'a, Token<'a>>>;

    let r#type = select! {
        Token::Identifier(ident) if ident == "i32" => ast::TypeKind::I32,
        Token::Identifier(ident) if ident == "i64" => ast::TypeKind::I64
    }
    .map_with(|kind, e: &mut MapExtra<'_, '_, I, E<'_>>| ast::Type {
        name: kind,
        location: ast::Location::from(e.span()),
    });

    let identifier = select! {
        Token::Identifier(ident) => ident,
    }
    .map_with(
        |ident, e: &mut MapExtra<'_, '_, I, E<'_>>| ast::Identifier {
            name: ident,
            location: ast::Location::from(e.span()),
        },
    );

    let literal = select! {
        Token::Integer(lit) => lit,
    }
    .map_with(
        |lit, e: &mut MapExtra<'_, '_, I, E<'_>>| ast::IntegerLiteral {
            value: lit,
            location: ast::Location::from(e.span()),
        },
    );

    let expression = recursive(|expression| {
        let function_call_args = expression
            .clone()
            .separated_by(just(Token::Comma))
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen));

        let function_call =
            identifier
                .clone()
                .then(function_call_args)
                .map_with(|(name, args), e| {
                    ast::Expression::FunctionCall(ast::FunctionCall {
                        name,
                        arguments: args,
                        location: ast::Location::from(e.span()),
                    })
                });

        let assignment = identifier
            .clone()
            .then_ignore(just(Token::Assign))
            .then(expression.clone())
            .map_with(|(name, value), e| {
                ast::Expression::AssignmentExpression(ast::AssignmentExpression {
                    name,
                    value: Box::new(value),
                    location: ast::Location::from(e.span()),
                })
            });

        let atom = literal
            .map(|lit| ast::Expression::IntegerLiteral(lit))
            .or(identifier.clone().map(|id| ast::Expression::Identifier(id)))
            .or(assignment)
            .or(function_call)
            .or(expression
                .clone()
                .delimited_by(just(Token::LParen), just(Token::RParen)));

        let unary = just(Token::Sub)
            .or(just(Token::Not))
            .repeated()
            .foldr(atom, |op, expr| {
                let op_kind = match op {
                    Token::Sub => ast::OperatorKind::Subtract,
                    Token::Not => ast::OperatorKind::LogicalNot,
                    _ => unreachable!(),
                };
                ast::Expression::UnaryExpression(ast::UnaryExpression {
                    operator: ast::Operator {
                        operator: op_kind,
                        location: ast::Location {
                            start: 0,
                            end: 0,
                            context: (),
                        },
                    },
                    operand: Box::new(expr),
                    location: ast::Location {
                        start: 0,
                        end: 0,
                        context: (),
                    },
                })
            });

        let mul = unary.clone().foldl(
            just(Token::Mul).or(just(Token::Div)).then(unary).repeated(),
            |left, (op, right)| {
                let op_kind = match op {
                    Token::Mul => ast::OperatorKind::Multiply,
                    Token::Div => ast::OperatorKind::Divide,
                    _ => unreachable!(),
                };
                ast::Expression::BinaryExpression(ast::BinaryExpression {
                    left: Box::new(left),
                    operator: ast::Operator {
                        operator: op_kind,
                        location: ast::Location {
                            start: 0,
                            end: 0,
                            context: (),
                        },
                    },
                    right: Box::new(right),
                    location: ast::Location {
                        start: 0,
                        end: 0,
                        context: (),
                    },
                })
            },
        );

        let add = mul.clone().foldl(
            just(Token::Add).or(just(Token::Sub)).then(mul).repeated(),
            |left, (op, right)| {
                let op_kind = match op {
                    Token::Add => ast::OperatorKind::Add,
                    Token::Sub => ast::OperatorKind::Subtract,
                    _ => unreachable!(),
                };
                ast::Expression::BinaryExpression(ast::BinaryExpression {
                    left: Box::new(left),
                    operator: ast::Operator {
                        operator: op_kind,
                        location: ast::Location {
                            start: 0,
                            end: 0,
                            context: (),
                        },
                    },
                    right: Box::new(right),
                    location: ast::Location {
                        start: 0,
                        end: 0,
                        context: (),
                    },
                })
            },
        );

        let comparison = add.clone().foldl(
            just(Token::LessThan)
                .or(just(Token::LessThanOrEqual))
                .or(just(Token::GreaterThan))
                .or(just(Token::GreaterThanOrEqual))
                .or(just(Token::Equal))
                .or(just(Token::NotEqual))
                .then(add)
                .repeated(),
            |left, (op, right)| {
                let op_kind = match op {
                    Token::LessThan => ast::OperatorKind::LessThan,
                    Token::LessThanOrEqual => ast::OperatorKind::LessThanOrEqual,
                    Token::GreaterThan => ast::OperatorKind::GreaterThan,
                    Token::GreaterThanOrEqual => ast::OperatorKind::GreaterThanOrEqual,
                    Token::Equal => ast::OperatorKind::Equal,
                    Token::NotEqual => ast::OperatorKind::NotEqual,
                    _ => unreachable!(),
                };
                ast::Expression::BinaryExpression(ast::BinaryExpression {
                    left: Box::new(left),
                    operator: ast::Operator {
                        operator: op_kind,
                        location: ast::Location {
                            start: 0,
                            end: 0,
                            context: (),
                        },
                    },
                    right: Box::new(right),
                    location: ast::Location {
                        start: 0,
                        end: 0,
                        context: (),
                    },
                })
            },
        );

        let logical = comparison.clone().foldl(
            just(Token::And)
                .or(just(Token::Or))
                .then(comparison)
                .repeated(),
            |left, (op, right)| {
                let op_kind = match op {
                    Token::And => ast::OperatorKind::LogicalAnd,
                    Token::Or => ast::OperatorKind::LogicalOr,
                    _ => unreachable!(),
                };
                ast::Expression::BinaryExpression(ast::BinaryExpression {
                    left: Box::new(left),
                    operator: ast::Operator {
                        operator: op_kind,
                        location: ast::Location {
                            start: 0,
                            end: 0,
                            context: (),
                        },
                    },
                    right: Box::new(right),
                    location: ast::Location {
                        start: 0,
                        end: 0,
                        context: (),
                    },
                })
            },
        );

        logical
    })
    .boxed();

    let statement = recursive(|_statement| {
        let variable_definition = just(Token::LetDeclaration)
            .or(just(Token::VarDeclaration))
            .then(identifier.clone())
            .then_ignore(just(Token::Colon))
            .then(r#type.clone())
            .then(just(Token::Assign).ignore_then(expression.clone()).or_not())
            .then_ignore(just(Token::Semicolon))
            .map_with(|(((keyword, name), var_type), value), e| {
                ast::Statement::VariableDefinition(ast::VariableDefinition {
                    name,
                    mutable: keyword == Token::VarDeclaration,
                    variable_type: var_type,
                    value,
                    location: ast::Location::from(e.span()),
                })
            });

        let expression_statement = expression
            .clone()
            .then_ignore(just(Token::Semicolon))
            .map_with(|expr, e| {
                ast::Statement::ExpressionStatement(ast::ExpressionStatement {
                    expression: expr,
                    location: ast::Location::from(e.span()),
                })
            });

        variable_definition.or(expression_statement)
    })
    .boxed();

    let block_without_expression = statement
        .clone()
        .repeated()
        .collect::<Vec<_>>()
        .map_with(|statements, e| ast::Block {
            statements: ast::Statements {
                statements,
                location: ast::Location::from(e.span()),
            },
            location: ast::Location::from(e.span()),
        })
        .delimited_by(just(Token::LBrace), just(Token::RBrace))
        .boxed();

    let block_with_expression = statement
        .clone()
        .repeated()
        .collect::<Vec<_>>()
        .then(expression.clone())
        .map_with(|(statements, final_expr), e| {
            let mut all_statements = statements;
            all_statements.push(ast::Statement::Expression(final_expr));
            ast::Block {
                statements: ast::Statements {
                    statements: all_statements,
                    location: ast::Location::from(e.span()),
                },
                location: ast::Location::from(e.span()),
            }
        })
        .delimited_by(just(Token::LBrace), just(Token::RBrace))
        .boxed();

    let parameter = identifier
        .clone()
        .then_ignore(just(Token::Colon))
        .then(r#type.clone())
        .map_with(|(name, param_type), e| ast::Parameter {
            name,
            parameter_type: param_type,
            location: ast::Location::from(e.span()),
        });

    let parameters = parameter
        .separated_by(just(Token::Comma))
        .collect::<Vec<_>>()
        .map_with(|params, e| ast::Parameters {
            parameters: params,
            location: ast::Location::from(e.span()),
        })
        .delimited_by(just(Token::LParen), just(Token::RParen));

    let function_definition = just(Token::FunctionDeclaration)
        .ignore_then(identifier.clone())
        .then(parameters)
        .then_ignore(just(Token::RightArrow))
        .then(r#type.clone())
        .then(block_with_expression.clone())
        .map_with(
            |(((name, params), return_type), body), e| ast::FunctionDefinition {
                name,
                parameters: params,
                return_type,
                body,
                location: ast::Location::from(e.span()),
            },
        );

    let program = function_definition
        .repeated()
        .collect::<Vec<_>>()
        .then_ignore(end())
        .map(|functions| ast::Program { functions });

    program
}

pub fn parse(src: &str) -> ParseResult<ast::Program, chumsky::error::Rich<'_, Token<'_>>> {
    // Create a logos lexer over the source code
    let token_iter = Token::lexer(src)
        .spanned()
        // Convert logos errors into tokens. We want parsing to be recoverable and not fail at the lexing stage, so
        // we have a dedicated `Token::Error` variant that represents a token error that was previously encountered
        .map(|(tok, span)| match tok {
            // Turn the `Range<usize>` spans logos gives us into chumsky's `SimpleSpan` via `Into`, because it's easier
            // to work with
            Ok(tok) => (tok, span.into()),
            Err(()) => (Token::Error, span.into()),
        });

    // Turn the token iterator into a stream that chumsky can use for things like backtracking
    let token_stream = chumsky::input::Stream::from_iter(token_iter)
        // Tell chumsky to split the (Token, SimpleSpan) stream into its parts so that it can handle the spans for us
        // This involves giving chumsky an 'end of input' span: we just use a zero-width span at the end of the string
        .map((0..src.len()).into(), |(t, s): (_, _)| (t, s));

    // Parse the token stream with our chumsky parser
    parser().parse(token_stream)
}

#[cfg(test)]
mod tests {
    use super::parse;
    use indoc::indoc;
    use insta::assert_yaml_snapshot;

    #[test]
    fn block_returns_none_when_multiple_expressions() {
        let source = indoc! {"
            {
                1
                2
            }
        "};
        let result = parse(source);
        assert!(result.errors().len() > 0);
    }

    #[test]
    fn block_returns_statements() {
        let source = indoc! {"
            {
                var x: i32;
                x = 0;
                x
            }
        "};
        let result = parse(source);
        assert!(result.errors().len() == 0);

        let ast = result.into_result().unwrap();
        assert_yaml_snapshot!(ast);
    }

    #[test]
    fn parse_returns_function_definition_without_parameters() {
        let source = indoc! {"
            fn main() -> i32 { 0 }
        "};
        let result = parse(source);
        assert!(result.errors().len() == 0);

        let ast = result.into_result().unwrap();
        assert_yaml_snapshot!(ast);
    }

    #[test]
    fn parse_returns_function_definition_with_parameters() {
        let source = indoc! {"
            fn add(x: i64, y: i64) -> i64 {
                x + y
            }
        "};
        let result = parse(source);
        assert!(result.errors().len() == 0);

        let ast = result.into_result().unwrap();
        assert_yaml_snapshot!(ast);
    }

    #[test]
    fn parse_returns_function_definitions() {
        let source = indoc! {"
            fn foo() -> i64 { 0 }
            fn bar() -> i32 { 1 }
        "};
        let result = parse(source);
        assert!(result.errors().len() == 0);

        let ast = result.into_result().unwrap();
        assert_yaml_snapshot!(ast);
    }

    #[test]
    fn parse_returns_function_when_comments() {
        let source = indoc! {"
            /// Main function
            fn main(/* empty */) -> i32 /* 0 or 1 */ {
                /* return */ 0 // return 0
            }
        "};
        let result = parse(source);
        assert!(result.errors().len() == 0);

        let ast = result.into_result().unwrap();
        assert_yaml_snapshot!(ast);
    }
}
