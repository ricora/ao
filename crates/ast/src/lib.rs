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
pub struct Program<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub functions: Vec<FunctionDefinition<'a, Ty>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionDefinition<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    #[serde(borrow)]
    pub parameters: Parameters<'a, Ty>,
    pub return_type: Ty,
    #[serde(borrow)]
    pub body: Block<'a, Ty>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Parameters<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub parameters: Vec<Parameter<'a, Ty>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Parameter<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    pub parameter_type: Ty,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub statements: Statements<'a, Ty>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Statements<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub statements: Vec<Statement<'a, Ty>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Statement<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    ExpressionStatement(ExpressionStatement<'a, Ty>),
    #[serde(borrow)]
    VariableDefinition(VariableDefinition<'a, Ty>),
    #[serde(borrow)]
    IfStatement(IfStatement<'a, Ty>),
    #[serde(borrow)]
    Expression(Expression<'a, Ty>),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExpressionStatement<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub expression: Expression<'a, Ty>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VariableDefinition<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    pub mutable: bool,
    pub variable_type: Ty,
    #[serde(borrow)]
    pub value: Option<Expression<'a, Ty>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IfStatement<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub condition: Expression<'a, Ty>,
    #[serde(borrow)]
    pub then_block: Block<'a, Ty>,
    #[serde(borrow)]
    pub else_block: Option<Block<'a, Ty>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expression<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    BinaryExpression(BinaryExpression<'a, Ty>),
    #[serde(borrow)]
    UnaryExpression(UnaryExpression<'a, Ty>),
    #[serde(borrow)]
    AssignmentExpression(AssignmentExpression<'a, Ty>),
    #[serde(borrow)]
    IdentifierExpression(IdentifierExpression<'a, Ty>),
    #[serde(borrow)]
    IntegerLiteral(IntegerLiteral<'a, Ty>),
    BooleanLiteral(BooleanLiteral<Ty>),
    #[serde(borrow)]
    FunctionCall(FunctionCall<'a, Ty>),
}

impl<'a> Expression<'a> {
    pub fn location(&self) -> &Location {
        match self {
            Expression::BinaryExpression(binary_expression) => &binary_expression.location,
            Expression::UnaryExpression(unary_expression) => &unary_expression.location,
            Expression::AssignmentExpression(assignment_expression) => {
                &assignment_expression.location
            }
            Expression::IdentifierExpression(identifier) => &identifier.location,
            Expression::IntegerLiteral(integer_literal) => &integer_literal.location,
            Expression::BooleanLiteral(boolean_literal) => &boolean_literal.location,
            Expression::FunctionCall(function_call) => &function_call.location,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinaryOperatorKind {
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
}

impl std::fmt::Display for BinaryOperatorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            BinaryOperatorKind::Add => write!(f, "+"),
            BinaryOperatorKind::Subtract => write!(f, "-"),
            BinaryOperatorKind::Multiply => write!(f, "*"),
            BinaryOperatorKind::Divide => write!(f, "/"),
            BinaryOperatorKind::LessThan => write!(f, "<"),
            BinaryOperatorKind::LessThanOrEqual => write!(f, "<="),
            BinaryOperatorKind::GreaterThan => write!(f, ">"),
            BinaryOperatorKind::GreaterThanOrEqual => write!(f, ">="),
            BinaryOperatorKind::Equal => write!(f, "=="),
            BinaryOperatorKind::NotEqual => write!(f, "!="),
            BinaryOperatorKind::LogicalAnd => write!(f, "&&"),
            BinaryOperatorKind::LogicalOr => write!(f, "||"),
        }
    }
}

impl std::str::FromStr for BinaryOperatorKind {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "+" => Ok(BinaryOperatorKind::Add),
            "-" => Ok(BinaryOperatorKind::Subtract),
            "*" => Ok(BinaryOperatorKind::Multiply),
            "/" => Ok(BinaryOperatorKind::Divide),
            "<" => Ok(BinaryOperatorKind::LessThan),
            "<=" => Ok(BinaryOperatorKind::LessThanOrEqual),
            ">" => Ok(BinaryOperatorKind::GreaterThan),
            ">=" => Ok(BinaryOperatorKind::GreaterThanOrEqual),
            "==" => Ok(BinaryOperatorKind::Equal),
            "!=" => Ok(BinaryOperatorKind::NotEqual),
            "&&" => Ok(BinaryOperatorKind::LogicalAnd),
            "||" => Ok(BinaryOperatorKind::LogicalOr),
            _ => Err("Invalid operator"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryOperator {
    pub operator: BinaryOperatorKind,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnaryOperatorKind {
    Negate,
    Not,
}

impl std::fmt::Display for UnaryOperatorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            UnaryOperatorKind::Negate => write!(f, "-"),
            UnaryOperatorKind::Not => write!(f, "!"),
        }
    }
}

impl std::str::FromStr for UnaryOperatorKind {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "-" => Ok(UnaryOperatorKind::Negate),
            "!" => Ok(UnaryOperatorKind::Not),
            _ => Err("Invalid unary operator"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnaryOperator {
    pub operator: UnaryOperatorKind,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BinaryExpression<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub left: Box<Expression<'a, Ty>>,
    pub operator: BinaryOperator,
    #[serde(borrow)]
    pub right: Box<Expression<'a, Ty>>,
    pub r#type: Ty,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnaryExpression<'a, Ty = Option<Type>> {
    pub operator: UnaryOperator,
    #[serde(borrow)]
    pub operand: Box<Expression<'a, Ty>>,
    pub r#type: Ty,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AssignmentExpression<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    #[serde(borrow)]
    pub value: Box<Expression<'a, Ty>>,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IdentifierExpression<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub identifier: Identifier<'a>,
    pub r#type: Ty,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Identifier<'a> {
    #[serde(borrow)]
    pub name: &'a str,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegerLiteral<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub value: &'a str,
    pub r#type: Ty,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BooleanLiteral<Ty = Option<Type>> {
    pub value: bool,
    pub r#type: Ty,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionCall<'a, Ty = Option<Type>> {
    #[serde(borrow)]
    pub name: Identifier<'a>,
    #[serde(borrow)]
    pub arguments: Vec<Expression<'a, Ty>>,
    pub r#type: Ty,
    pub location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypeKind {
    I32,
    I64,
    Bool,
    Unit,
}

impl std::fmt::Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TypeKind::I32 => write!(f, "i32"),
            TypeKind::I64 => write!(f, "i64"),
            TypeKind::Bool => write!(f, "bool"),
            TypeKind::Unit => write!(f, "()"),
        }
    }
}

impl std::str::FromStr for TypeKind {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "i32" => Ok(TypeKind::I32),
            "i64" => Ok(TypeKind::I64),
            "bool" => Ok(TypeKind::Bool),
            "()" => Ok(TypeKind::Unit),
            _ => Err("Invalid type"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Type {
    pub kind: TypeKind,
    pub location: Location,
}

pub type TypedExpression<'a> = Expression<'a, Type>;
pub type TypedStatement<'a> = Statement<'a, Type>;
pub type TypedBlock<'a> = Block<'a, Type>;
pub type TypedParameters<'a> = Parameters<'a, Type>;
pub type TypedParameter<'a> = Parameter<'a, Type>;
pub type TypedFunctionDefinition<'a> = FunctionDefinition<'a, Type>;
pub type TypedProgram<'a> = Program<'a, Type>;
