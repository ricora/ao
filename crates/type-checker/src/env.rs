use ast::TypeKind;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct VariableInfo {
    pub var_type: TypeKind,
    pub mutable: bool,
    pub initialized: bool,
}

#[derive(Debug, Clone)]
pub struct FunctionInfo {
    pub parameters: Vec<TypeKind>,
    pub return_type: TypeKind,
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
                var_type: TypeKind::I32,
                mutable: false,
                initialized: true,
            },
        );

        let var_info = env.get_variable("x").unwrap();
        assert_eq!(var_info.var_type, TypeKind::I32);
        assert!(!var_info.mutable);
        assert!(var_info.initialized);
    }

    #[test]
    fn test_block_scoping() {
        let mut env = TypeEnvironment::new();

        // Add variable 'x' in outer scope
        env.push_scope();
        env.add_variable(
            "x".to_string(),
            VariableInfo {
                var_type: TypeKind::I32,
                mutable: false,
                initialized: true,
            },
        );

        // Enter inner scope
        env.push_scope();
        env.add_variable(
            "y".to_string(),
            VariableInfo {
                var_type: TypeKind::I64,
                mutable: false,
                initialized: true,
            },
        );

        // Both variables should be accessible
        assert!(env.get_variable("x").is_some());
        assert!(env.get_variable("y").is_some());

        // Exit inner scope
        env.pop_scope();

        // Only outer variable should be accessible
        assert!(env.get_variable("x").is_some());
        assert!(env.get_variable("y").is_none());

        env.pop_scope();
    }

    #[test]
    fn test_nested_block_scopes() {
        let mut env = TypeEnvironment::new();

        // Global scope
        env.add_variable(
            "global".to_string(),
            VariableInfo {
                var_type: TypeKind::I32,
                mutable: false,
                initialized: true,
            },
        );

        // Level 1 scope
        env.push_scope();
        env.add_variable(
            "level1".to_string(),
            VariableInfo {
                var_type: TypeKind::I64,
                mutable: false,
                initialized: true,
            },
        );

        // Level 2 scope
        env.push_scope();
        env.add_variable(
            "level2".to_string(),
            VariableInfo {
                var_type: TypeKind::Bool,
                mutable: false,
                initialized: true,
            },
        );

        // All variables should be accessible from deepest scope
        assert!(env.get_variable("global").is_some());
        assert!(env.get_variable("level1").is_some());
        assert!(env.get_variable("level2").is_some());

        // Pop level 2
        env.pop_scope();
        assert!(env.get_variable("global").is_some());
        assert!(env.get_variable("level1").is_some());
        assert!(env.get_variable("level2").is_none());

        // Pop level 1
        env.pop_scope();
        assert!(env.get_variable("global").is_some());
        assert!(env.get_variable("level1").is_none());
        assert!(env.get_variable("level2").is_none());
    }

    #[test]
    fn test_variable_shadowing() {
        let mut env = TypeEnvironment::new();

        // Add variable 'x' in outer scope
        env.add_variable(
            "x".to_string(),
            VariableInfo {
                var_type: TypeKind::I32,
                mutable: false,
                initialized: true,
            },
        );

        // Verify outer variable
        assert_eq!(env.get_variable("x").unwrap().var_type, TypeKind::I32);

        // Enter inner scope and shadow 'x'
        env.push_scope();
        env.add_variable(
            "x".to_string(),
            VariableInfo {
                var_type: TypeKind::I64,
                mutable: true,
                initialized: true,
            },
        );

        // Should see inner variable (shadowing)
        let var_info = env.get_variable("x").unwrap();
        assert_eq!(var_info.var_type, TypeKind::I64);
        assert!(var_info.mutable);

        // Exit inner scope
        env.pop_scope();

        // Should see outer variable again
        let var_info = env.get_variable("x").unwrap();
        assert_eq!(var_info.var_type, TypeKind::I32);
        assert!(!var_info.mutable);
    }

    #[test]
    fn test_function_management() {
        let mut env = TypeEnvironment::new();

        env.add_function(
            "test_func".to_string(),
            FunctionInfo {
                parameters: vec![TypeKind::I32, TypeKind::I64],
                return_type: TypeKind::Bool,
            },
        );

        let func_info = env.get_function("test_func").unwrap();
        assert_eq!(func_info.parameters, vec![TypeKind::I32, TypeKind::I64]);
        assert_eq!(func_info.return_type, TypeKind::Bool);

        assert!(env.get_function("nonexistent").is_none());
    }

    #[test]
    fn test_variable_exists_in_current_scope() {
        let mut env = TypeEnvironment::new();

        // Add to global scope
        env.add_variable(
            "global".to_string(),
            VariableInfo {
                var_type: TypeKind::I32,
                mutable: false,
                initialized: true,
            },
        );

        assert!(env.variable_exists_in_current_scope("global"));

        // Push new scope
        env.push_scope();

        // Global variable should not exist in current scope
        assert!(!env.variable_exists_in_current_scope("global"));

        // Add to current scope
        env.add_variable(
            "local".to_string(),
            VariableInfo {
                var_type: TypeKind::I64,
                mutable: false,
                initialized: true,
            },
        );

        assert!(env.variable_exists_in_current_scope("local"));
        assert!(!env.variable_exists_in_current_scope("global"));
    }
}
