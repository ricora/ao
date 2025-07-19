use std::collections::HashMap;
use ast::TypeKind;

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
    pub variable_scopes: Vec<HashMap<String, VariableInfo>>,
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

impl Default for TypeEnvironment {
    fn default() -> Self {
        Self::new()
    }
}