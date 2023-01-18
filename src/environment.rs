pub struct Environment {
    declarations: HashMap<String, AcornType>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            declarations: HashMap::from([
                ("bool", AcornType::Bool),
                ("nat", AcornType::Nat),
                ("int", AcornType::Int),
            ]),
        }
    }

    pub fn declare(&mut self, name: &str, acorn_type: AcornType) {
        self.declarations.insert(name.to_string(), acorn_type);
    }

    pub fn lookup(&self, name: &str) -> Option<&AcornType> {
        self.declarations.get(name)
    }
}
