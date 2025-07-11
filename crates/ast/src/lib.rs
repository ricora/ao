use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Location<T = usize, C = ()> {
    /// The start position of the location in the source code
    pub start: T,
    /// The end position of the location in the source code
    pub end: T,
    /// Additional context for the location, if any
    pub context: C,
}

impl From<chumsky::span::SimpleSpan> for Location {
    fn from(span: chumsky::span::SimpleSpan) -> Self {
        Location {
            start: span.start,
            end: span.end,
            context: span.context,
        }
    }
}

impl Location {
    pub fn to_range(&self) -> std::ops::Range<usize> {
        self.start..self.end
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Program<'a> {
    #[serde(borrow)]
    pub functions: Vec<FunctionDefinition<'a>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionDefinition<'a> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    #[serde(borrow)]
    pub parameters: Parameters<'a>,
    pub return_type: Type,
    #[serde(borrow)]
    pub body: Block<'a>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Parameters<'a> {
    #[serde(borrow)]
    pub parameters: Vec<Parameter<'a>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Parameter<'a> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    pub parameter_type: Type,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block<'a> {
    #[serde(borrow)]
    pub statements: Statements<'a>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Statements<'a> {
    #[serde(borrow)]
    pub statements: Vec<Statement<'a>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Statement<'a> {
    #[serde(borrow)]
    ExpressionStatement(ExpressionStatement<'a>),
    #[serde(borrow)]
    VariableDefinition(VariableDefinition<'a>),
    #[serde(borrow)]
    IfStatement(IfStatement<'a>),
    #[serde(borrow)]
    Expression(Expression<'a>),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpressionStatement<'a> {
    #[serde(borrow)]
    pub expression: Expression<'a>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VariableDefinition<'a> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    pub mutable: bool,
    pub variable_type: Type,
    #[serde(borrow)]
    pub value: Option<Expression<'a>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IfStatement<'a> {
    #[serde(borrow)]
    pub condition: Expression<'a>,
    #[serde(borrow)]
    pub then_block: Block<'a>,
    #[serde(borrow)]
    pub else_block: Option<Block<'a>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expression<'a> {
    #[serde(borrow)]
    BinaryExpression(BinaryExpression<'a>),
    #[serde(borrow)]
    UnaryExpression(UnaryExpression<'a>),
    #[serde(borrow)]
    AssignmentExpression(AssignmentExpression<'a>),
    #[serde(borrow)]
    Identifier(Identifier<'a>),
    #[serde(borrow)]
    IntegerLiteral(IntegerLiteral<'a>),
    #[serde(borrow)]
    FunctionCall(FunctionCall<'a>),
}

impl<'a> Expression<'a> {
    pub fn location(&self) -> &Location {
        match self {
            Expression::BinaryExpression(binary_expression) => &binary_expression.location,
            Expression::UnaryExpression(unary_expression) => &unary_expression.location,
            Expression::AssignmentExpression(assignment_expression) => {
                &assignment_expression.location
            }
            Expression::Identifier(identifier) => &identifier.location,
            Expression::IntegerLiteral(integer_literal) => &integer_literal.location,
            Expression::FunctionCall(function_call) => &function_call.location,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OperatorKind {
    Add,
    Subtract,
    Multiply,
    Divide,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Equal,
    NotEqual,
    LogicalAnd,
    LogicalOr,
    LogicalNot,
}

impl std::fmt::Display for OperatorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            OperatorKind::Add => write!(f, "+"),
            OperatorKind::Subtract => write!(f, "-"),
            OperatorKind::Multiply => write!(f, "*"),
            OperatorKind::Divide => write!(f, "/"),
            OperatorKind::LessThan => write!(f, "<"),
            OperatorKind::LessThanOrEqual => write!(f, "<="),
            OperatorKind::GreaterThan => write!(f, ">"),
            OperatorKind::GreaterThanOrEqual => write!(f, ">="),
            OperatorKind::Equal => write!(f, "=="),
            OperatorKind::NotEqual => write!(f, "!="),
            OperatorKind::LogicalAnd => write!(f, "&&"),
            OperatorKind::LogicalOr => write!(f, "||"),
            OperatorKind::LogicalNot => write!(f, "!"),
        }
    }
}

impl std::str::FromStr for OperatorKind {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "+" => Ok(OperatorKind::Add),
            "-" => Ok(OperatorKind::Subtract),
            "*" => Ok(OperatorKind::Multiply),
            "/" => Ok(OperatorKind::Divide),
            "<" => Ok(OperatorKind::LessThan),
            "<=" => Ok(OperatorKind::LessThanOrEqual),
            ">" => Ok(OperatorKind::GreaterThan),
            ">=" => Ok(OperatorKind::GreaterThanOrEqual),
            "==" => Ok(OperatorKind::Equal),
            "!=" => Ok(OperatorKind::NotEqual),
            "&&" => Ok(OperatorKind::LogicalAnd),
            "||" => Ok(OperatorKind::LogicalOr),
            "!" => Ok(OperatorKind::LogicalNot),
            _ => Err("Invalid operator"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Operator {
    pub operator: OperatorKind,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryExpression<'a> {
    #[serde(borrow)]
    pub left: Box<Expression<'a>>,
    pub operator: Operator,
    #[serde(borrow)]
    pub right: Box<Expression<'a>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnaryExpression<'a> {
    pub operator: Operator,
    #[serde(borrow)]
    pub operand: Box<Expression<'a>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AssignmentExpression<'a> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    #[serde(borrow)]
    pub value: Box<Expression<'a>>,
    pub location: Location,
}


#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Identifier<'a> {
    #[serde(borrow)]
    pub name: &'a str,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegerLiteral<'a> {
    #[serde(borrow)]
    pub value: &'a str,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionCall<'a> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    #[serde(borrow)]
    pub arguments: Vec<Expression<'a>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypeKind {
    I32,
    I64,
}

impl std::fmt::Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TypeKind::I32 => write!(f, "i32"),
            TypeKind::I64 => write!(f, "i64"),
        }
    }
}

impl std::str::FromStr for TypeKind {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "i32" => Ok(TypeKind::I32),
            "i64" => Ok(TypeKind::I64),
            _ => Err("Invalid type"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Type {
    pub name: TypeKind,
    pub location: Location,
}
