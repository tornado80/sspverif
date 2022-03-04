use super::errors::ScopeError;
use crate::identifier::Identifier;
use crate::types::Type;
use std::collections::HashMap;

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

    pub fn leave(&mut self) {
        if !self.0.is_empty() {
            self.0.pop();
        } else {
            panic!("scope leave: scope stack is empty");
        }
    }

    /* Error conditions:
     *  - No scope at all
     *  - Identifier exists somewhere in the scope tower already
     */
    pub fn declare(&mut self, id: Identifier, t: Type) -> Result<(), ScopeError> {
        //let bt = Backtrace::capture();
        //println!("declaring: {:?} {:?} {}", id, t, bt);
        if self.lookup(&id) == None {
            if let Some(last) = self.0.last_mut() {
                last.insert(id, t);
                Ok(())
            } else {
                panic!("scope declare: scope stack is empty");
            }
        } else {
            Err(ScopeError) // already defined
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

#[cfg(test)]
mod test {
    use crate::identifier::Identifier;
    use crate::types::Type;

    use super::Scope;

    /* Properties:
    - (enter then) only lookup -> fails trivially (not tested)
    - (enter then) declare then lookup -> success
    - access variable that was declared inside a block after leaving -> fails
    - access varable that was declared, then enter and leave -> success
    */

    #[test]
    fn declare_then_lookup_succeeds() {
        let id = Identifier::Local("test_id".to_string());
        let t = Type::Integer;

        let mut scope = Scope::new();
        scope.enter();
        scope
            .declare(id.clone(), t.clone())
            .expect("declare failed");
        let t_ = scope.lookup(&id).expect("lookup failed");

        assert_eq!(t, t_, "lookup returned wrong type");
    }

    #[test]
    fn gone_after_leave() {
        let id = Identifier::Local("test_id".to_string());
        let t = Type::Integer;

        let mut scope = Scope::new();
        scope.enter();
        scope.enter();
        scope
            .declare(id.clone(), t.clone())
            .expect("declare failed");
        scope.leave();

        assert_eq!(None, scope.lookup(&id));
    }

    #[test]
    fn still_there_after_enter_and_leave() {
        let id = Identifier::Local("test_id".to_string());
        let id2 = Identifier::Local("test_id2".to_string());
        let t = Type::Integer;
        let t2 = Type::String;

        let mut scope = Scope::new();
        scope.enter();
        scope
            .declare(id.clone(), t.clone())
            .expect("declare id failed");

        scope.enter();
        scope.declare(id2, t2).expect("declare id2 failed");
        scope.leave();

        let t_ = scope.lookup(&id).expect("lookup failed");

        assert_eq!(t, t_, "lookup returned wrong type");
    }
}
