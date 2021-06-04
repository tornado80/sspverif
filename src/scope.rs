use std::collections::HashMap;

use crate::types::Type;
use crate::identifier::Identifier;

#[derive(Debug)]
pub struct ScopeError;

// TODO
#[derive(Debug, Clone)]
pub struct Scope(Vec<HashMap<Identifier, Type>>);

impl Scope {
    pub fn new() -> Scope {
        Scope(vec![])
    }

    pub fn enter(&mut self) {
        self.0.push(HashMap::new())
    }

    pub fn leave(&mut self) -> Result<(), ScopeError> {
        if self.0.len() > 0 {
            self.0.pop();
            Ok(())
        } else {
            Err(ScopeError)
        }
    }

    /* Error conditions:
     *  - No scope at all
     *  - Identifier exists somewhere in the scope tower already
     */
    pub fn declare(&mut self, id: Identifier, t: Type) -> Result<(), ScopeError> {
        if self.lookup(&id) == None {
            if let Some(mut last) = self.0.last_mut() {
                last.insert(id, t);
                Ok(())
            } else {
                Err(ScopeError)
            }
        } else {
            Err(ScopeError)
        }
    }

    pub fn lookup(&self, id: &Identifier) -> Option<Type> {
        for table in self.0.clone().into_iter().rev() {
            if let Some(t) = table.get(id) {
                return Some(t.clone());
            }
        }

        None
    }
}
