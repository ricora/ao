mod token;

use chumsky::{input::ValueInput, prelude::*};
use logos::Logos;
use token::Token;

pub fn parser<'a, I>() -> impl Parser<'a, I, ast::Program<'a>, extra::Err<Rich<'a, Token<'a>>>>
where
    I: ValueInput<'a, Token = Token<'a>, Span = SimpleSpan>,
{
    let identifier = select! {
        Token::Identifier(ident) => ident,
    }
    .map_with(|ident, e| ast::Identifier {
        name: ident,
        location: ast::Location::from(e.span()),
    });

    // TODO: Implement the full parser for the AST
    identifier
        .then_ignore(end())
        .map(|_| ast::Program { functions: vec![] }) // TODO: Replace with actual function definitions
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
