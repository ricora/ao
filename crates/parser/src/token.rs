use logos::Logos;

#[derive(Logos, Clone, PartialEq, Debug)]
pub enum Token<'a> {
    Error,

    #[token("fn")]
    FunctionDeclaration,

    #[token("let")]
    LetDeclaration,

    #[token("var")]
    VarDeclaration,

    #[token("if")]
    If,

    #[token("else")]
    Else,

    #[token("while")]
    While,

    #[token("for")]
    For,

    #[token("return")]
    Return,

    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*")]
    Identifier(&'a str),

    #[regex(r"[0-9]+")]
    Integer(&'a str),

    #[token("true")]
    True,
    #[token("false")]
    False,

    #[token("+")]
    Add,

    #[token("-")]
    Sub,

    #[token("*")]
    Mul,

    #[token("/")]
    Div,

    #[token("==")]
    Equal,

    #[token("!=")]
    NotEqual,

    #[token("<")]
    LessThan,

    #[token("<=")]
    LessThanOrEqual,

    #[token(">")]
    GreaterThan,

    #[token(">=")]
    GreaterThanOrEqual,

    #[token("&&")]
    And,

    #[token("||")]
    Or,

    #[token("!")]
    Not,

    #[token(",")]
    Comma,

    #[token("->")]
    RightArrow,

    #[token(":")]
    Colon,

    #[token(";")]
    Semicolon,

    #[token("=")]
    Assign,

    #[token("(")]
    LParen,
    #[token(")")]
    RParen,

    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,

    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,

    #[regex(r"[ \t\f\n]+", logos::skip)]
    Whitespace,

    // Skip line comments (// ...)
    #[regex(r"//.*", logos::skip)]
    LineComment,

    // Skip block comments (/* ... */)
    #[regex(r"/\*[^*]*\*+(?:[^/*][^*]*\*+)*/", logos::skip)]
    BlockComment,
}

impl std::fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FunctionDeclaration => write!(f, "fn"),
            Self::LetDeclaration => write!(f, "let"),
            Self::VarDeclaration => write!(f, "var"),
            Self::If => write!(f, "if"),
            Self::Else => write!(f, "else"),
            Self::While => write!(f, "while"),
            Self::For => write!(f, "for"),
            Self::Return => write!(f, "return"),
            Self::Identifier(value) => write!(f, "{value}"),
            Self::Integer(value) => write!(f, "{value}"),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div => write!(f, "/"),
            Self::Equal => write!(f, "=="),
            Self::NotEqual => write!(f, "!="),
            Self::LessThan => write!(f, "<"),
            Self::LessThanOrEqual => write!(f, "<="),
            Self::GreaterThan => write!(f, ">"),
            Self::GreaterThanOrEqual => write!(f, ">="),
            Self::And => write!(f, "&&"),
            Self::Or => write!(f, "||"),
            Self::Not => write!(f, "!"),
            Self::Comma => write!(f, ","),
            Self::Colon => write!(f, ":"),
            Self::Semicolon => write!(f, ";"),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::LBrace => write!(f, "{{"),
            Self::RBrace => write!(f, "}}"),
            Self::LBracket => write!(f, "["),
            Self::RBracket => write!(f, "]"),
            Self::RightArrow => write!(f, "->"),
            Self::Assign => write!(f, "="),
            Self::Whitespace => write!(f, "<whitespace>"),
            Self::LineComment => write!(f, "<line_comment>"),
            Self::BlockComment => write!(f, "<block_comment>"),
            Self::Error => write!(f, "<e>"),
        }
    }
}
