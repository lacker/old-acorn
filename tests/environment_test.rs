#[cfg(test)]
mod environment_test {
    use acorn::environment::Environment;
    use acorn::project::Project;

    #[test]
    fn test_fn_equality() {
        let mut env = Environment::new_test();
        env.add("define idb1(x: Bool) -> Bool { x }");
        env.expect_type("idb1", "Bool -> Bool");
        env.add("define idb2(y: Bool) -> Bool { y }");
        env.expect_type("idb2", "Bool -> Bool");
        env.assert_def_eq("idb1", "idb2");

        env.add("type Nat: axiom");
        env.add("define idn1(x: Nat) -> Nat { x }");
        env.expect_type("idn1", "Nat -> Nat");
        env.assert_def_ne("idb1", "idn1");
    }

    #[test]
    fn test_forall_equality() {
        let mut env = Environment::new_test();
        env.add("let bsym1: Bool = forall(x: Bool) { x = x }");
        env.expect_type("bsym1", "Bool");
        env.add("let bsym2: Bool = forall(y: Bool) { y = y }");
        env.expect_type("bsym2", "Bool");
        env.assert_def_eq("bsym1", "bsym2");

        env.add("type Nat: axiom");
        env.add("let nsym1: Bool = forall(x: Nat) { x = x }");
        env.expect_type("nsym1", "Bool");
        env.assert_def_ne("bsym1", "nsym1");
    }

    #[test]
    fn test_exists_equality() {
        let mut env = Environment::new_test();
        env.add("let bex1: Bool = exists(x: Bool) { x = x }");
        env.add("let bex2: Bool = exists(y: Bool) { y = y }");
        env.assert_def_eq("bex1", "bex2");

        env.add("type Nat: axiom");
        env.add("let nex1: Bool = exists(x: Nat) { x = x }");
        env.assert_def_ne("bex1", "nex1");
    }

    #[test]
    fn test_arg_binding() {
        let mut env = Environment::new_test();
        env.bad("define qux(x: Bool, x: Bool) -> Bool { x }");
        assert!(!env.bindings.has_identifier("x"));
        env.add("define qux(x: Bool, y: Bool) -> Bool { x }");
        env.expect_type("qux", "(Bool, Bool) -> Bool");

        env.bad("theorem foo(x: Bool, x: Bool) { x }");
        assert!(!env.bindings.has_identifier("x"));
        env.add("theorem foo(x: Bool, y: Bool) { x }");
        env.expect_type("foo", "(Bool, Bool) -> Bool");

        env.bad("let bar: Bool = forall(x: Bool, x: Bool) { x = x }");
        assert!(!env.bindings.has_identifier("x"));
        env.add("let bar: Bool = forall(x: Bool, y: Bool) { x = x }");

        env.bad("let baz: Bool = exists(x: Bool, x: Bool) { x = x }");
        assert!(!env.bindings.has_identifier("x"));
        env.add("let baz: Bool = exists(x: Bool, y: Bool) { x = x }");
    }

    #[test]
    fn test_no_double_grouped_arg_list() {
        let mut env = Environment::new_test();
        env.add("define foo(x: Bool, y: Bool) -> Bool { x }");
        env.add("let b: Bool = axiom");
        env.bad("foo((b, b))");
    }

    #[test]
    fn test_argless_theorem() {
        let mut env = Environment::new_test();
        env.add("let b: Bool = axiom");
        env.add("theorem foo { b or not b }");
        env.expect_def("foo", "(b or not b)");
    }

    #[test]
    fn test_forall_value() {
        let mut env = Environment::new_test();
        env.add("let p: Bool = forall(x: Bool) { x or not x }");
        env.expect_def("p", "forall(x0: Bool) { (x0 or not x0) }");
    }

    #[test]
    fn test_inline_function_value() {
        let mut env = Environment::new_test();
        env.add("define ander(a: Bool) -> (Bool -> Bool) { function(b: Bool) { a and b } }");
        env.expect_def(
            "ander",
            "function(x0: Bool) { function(x1: Bool) { (x0 and x1) } }",
        );
    }

    #[test]
    fn test_empty_if_block() {
        let mut env = Environment::new_test();
        env.add("let b: Bool = axiom");
        env.add("if b {}");
    }

    #[test]
    fn test_empty_forall_statement() {
        // Allowed as statement but not as an expression.
        let mut env = Environment::new_test();
        env.add("forall(b: Bool) {}");
    }

    #[test]
    fn test_nat_ac_piecewise() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let zero: Nat = axiom");
        env.add("let suc: Nat -> Nat = axiom");
        env.add("let one: Nat = suc(zero)");
        env.expect_def("one", "suc(zero)");

        env.add("axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) -> x = y }");
        env.expect_type("suc_injective", "(Nat, Nat) -> Bool");
        env.expect_def(
            "suc_injective",
            "function(x0: Nat, x1: Nat) { ((suc(x0) = suc(x1)) -> (x0 = x1)) }",
        );

        env.add("axiom suc_neq_zero(x: Nat) { suc(x) != zero }");
        env.expect_def("suc_neq_zero", "function(x0: Nat) { (suc(x0) != zero) }");

        assert!(env.bindings.has_type_name("Nat"));
        assert!(!env.bindings.has_identifier("Nat"));

        assert!(!env.bindings.has_type_name("zero"));
        assert!(env.bindings.has_identifier("zero"));

        assert!(!env.bindings.has_type_name("one"));
        assert!(env.bindings.has_identifier("one"));

        assert!(!env.bindings.has_type_name("suc"));
        assert!(env.bindings.has_identifier("suc"));

        assert!(!env.bindings.has_type_name("foo"));
        assert!(!env.bindings.has_identifier("foo"));

        env.add(
            "axiom induction(f: Nat -> Bool, n: Nat) {
            f(zero) and forall(k: Nat) { f(k) -> f(suc(k)) } -> f(n) }",
        );
        env.expect_def("induction", "function(x0: Nat -> Bool, x1: Nat) { ((x0(zero) and forall(x2: Nat) { (x0(x2) -> x0(suc(x2))) }) -> x0(x1)) }");

        env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }");
        env.expect_type("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

        env.add("axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }");
        env.add(
            "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) {
            recursion(f, a, suc(n)) = f(recursion(f, a, n)) }",
        );

        env.add("define add(a: Nat, b: Nat) -> Nat { recursion(suc, a, b) }");
        env.expect_type("add", "(Nat, Nat) -> Nat");

        env.add("theorem add_zero_right(a: Nat) { add(a, zero) = a }");
        env.add("theorem add_zero_left(a: Nat) { add(zero, a) = a }");
        env.add("theorem add_suc_right(a: Nat, b: Nat) { add(a, suc(b)) = suc(add(a, b)) }");
        env.add("theorem add_suc_left(a: Nat, b: Nat) { add(suc(a), b) = suc(add(a, b)) }");
        env.add("theorem add_comm(a: Nat, b: Nat) { add(a, b) = add(b, a) }");
        env.add(
            "theorem add_assoc(a: Nat, b: Nat, c: Nat) { add(add(a, b), c) = add(a, add(b, c)) }",
        );
        env.add("theorem not_suc_eq_zero(x: Nat) { not (suc(x) = zero) }");
    }

    #[test]
    fn test_nat_ac_together() {
        let mut env = Environment::new_test();
        env.add(
            r#"
// The axioms of Peano arithmetic.
        
type Nat: axiom

let zero: Nat = axiom

let suc: Nat -> Nat = axiom
let one: Nat = suc(zero)

axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) -> x = y }

axiom suc_neq_zero(x: Nat) { suc(x) != zero }

axiom induction(f: Nat -> Bool) { f(zero) and forall(k: Nat) { f(k) -> f(suc(k)) } -> forall(n: Nat) { f(n) } }

// The old version. In the modern codebase these are parametric.
define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }
axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }
axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) { recursion(f, a, suc(n)) = f(recursion(f, a, n)) }

define add(a: Nat, b: Nat) -> Nat { recursion(suc, a, b) }

// Now let's have some theorems.

theorem add_zero_right(a: Nat) { add(a, zero) = a }

theorem add_zero_left(a: Nat) { add(zero, a) = a }

theorem add_suc_right(a: Nat, b: Nat) { add(a, suc(b)) = suc(add(a, b)) }

theorem add_suc_left(a: Nat, b: Nat) { add(suc(a), b) = suc(add(a, b)) }

theorem add_comm(a: Nat, b: Nat) { add(a, b) = add(b, a) }

theorem add_assoc(a: Nat, b: Nat, c: Nat) { add(add(a, b), c) = add(a, add(b, c)) }
"#,
        );
    }

    #[test]
    fn test_names_in_subenvs() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            theorem foo(a: Nat, b: Nat) { a = b } by {
                let c: Nat = a
                define d(e: Nat) -> Bool { foo(e, b) }
            }
            "#,
        );
        env.check_lines();
    }

    #[test]
    fn test_forall_subenv() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            forall(x: Nat) {
                x = x
            }
            "#,
        );
    }

    #[test]
    fn test_if_subenv() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            if zero = zero {
                zero = zero
            }
            "#,
        )
    }

    #[test]
    fn test_let_satisfy_exports_names() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            define foo(x: Nat) -> Bool { axiom }
            theorem goal { true } by {
                let z: Nat satisfy { foo(z) }
                foo(z)
            }
        "#,
        );
    }

    #[test]
    fn test_environment_with_function_satisfy() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let flip(a: Bool) -> b: Bool satisfy {
                a != b
            }
        "#,
        );
    }

    #[test]
    fn test_if_block_ending_with_exists() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            let a: Bool = axiom
            theorem goal { a } by {
                if a {
                    exists(b: Bool) { b = b }
                }
            }
            "#,
        );
        let module = p.expect_ok("main");
        let env = p.get_env(module).unwrap();
        for node in env.iter_goals() {
            node.goal_context().unwrap();
        }
    }

    #[test]
    fn test_forall_block_ending_with_exists() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            let a: Bool = axiom
            theorem goal { a } by {
                forall(b: Bool) {
                    exists(c: Bool) { c = c }
                }
            }
            "#,
        );
        let module = p.expect_ok("main");
        let env = p.get_env(module).unwrap();
        for node in env.iter_goals() {
            node.goal_context().unwrap();
        }
    }

    #[test]
    fn test_structure_new_definition() {
        let mut env = Environment::new_test();
        env.add(
            r#"
        structure BoolPair {
            first: Bool
            second: Bool
        }
        theorem goal(p: BoolPair) {
            p = BoolPair.new(BoolPair.first(p), BoolPair.second(p))
        }
        "#,
        );
    }

    #[test]
    fn test_structure_cant_contain_itself() {
        // If you want a type to contain itself, it has to be inductive, not a structure.
        let mut env = Environment::new_test();
        env.bad(
            r#"
        structure InfiniteBools {
            head: Bool
            tail: InfiniteBools
        }
        "#,
        );
    }

    #[test]
    fn test_inductive_new_definition() {
        let mut env = Environment::new_test();
        env.add(
            r#"
        inductive Nat {
            zero
            suc(Nat)
        }
        theorem goal(n: Nat) {
            n = Nat.zero or exists(k: Nat) { n = Nat.suc(k) }
        }
        "#,
        );
    }

    #[test]
    fn test_inductive_constructor_can_be_member() {
        let mut env = Environment::new_test();
        env.add(
            r#"
        inductive Nat {
            zero
            suc(Nat)
        }
        theorem goal(n: Nat) {
            n = Nat.zero or exists(k: Nat) { n = k.suc }
        }
        "#,
        );
    }

    #[test]
    fn test_inductive_statements_must_have_base_case() {
        let mut env = Environment::new_test();
        env.bad(
            r#"
        inductive Nat {
            suc(Nat)
        }"#,
        );
    }

    #[test]
    fn test_no_russell_paradox() {
        let mut env = Environment::new_test();
        env.bad(
            r#"
        structure NaiveSet {
            set: NaiveSet -> Bool 
        }
        "#,
        );
    }

    #[test]
    fn test_parametric_types_required_in_function_args() {
        let mut env = Environment::new_test();
        env.bad("define foo<T>(a: Bool) -> Bool { a }");
    }

    #[test]
    fn test_parametric_types_required_in_theorem_args() {
        let mut env = Environment::new_test();
        env.bad("theorem foo<T>(a: Bool) { a or not a }");
    }

    #[test]
    fn test_template_typechecking() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let zero: Nat = axiom");
        env.add("define eq<T>(a: T, b: T) -> Bool { a = b }");
        env.add("theorem t1 { eq(zero, zero) }");
        env.add("theorem t2 { eq(zero = zero, zero = zero) }");
        env.add("theorem t3 { eq(zero = zero, eq(zero, zero)) }");
        env.bad("theorem t4 { eq(zero, zero = zero) }");
        env.bad("theorem t5 { zero = eq(zero, zero) }");
    }

    #[test]
    fn test_type_params_cleaned_up() {
        let mut env = Environment::new_test();
        env.add("define foo<T>(a: T) -> Bool { axiom }");
        assert!(env.bindings.get_type_for_name("T").is_none());
    }

    #[test]
    fn test_if_condition_must_be_bool() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let zero: Nat = axiom");
        env.add("let b: Bool = axiom");
        env.add("if b { zero = zero }");
        env.bad("if zero { zero = zero }");
    }

    #[test]
    fn test_reusing_type_name_as_var_name() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let Nat: Bool = axiom");
    }

    #[test]
    fn test_reusing_var_name_as_type_name() {
        let mut env = Environment::new_test();
        env.add("let x: Bool = axiom");
        env.bad("type x: axiom");
    }

    #[test]
    fn test_reusing_type_name_as_fn_name() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("define Nat(x: Bool) -> Bool { x }");
    }

    #[test]
    fn test_reusing_type_name_as_theorem_name() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("theorem Nat(x: Bool): x = x");
    }

    #[test]
    fn test_reusing_type_name_as_exists_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let b: Bool = exists(x: Bool, Nat: Bool) { x = x }");
    }

    #[test]
    fn test_reusing_type_name_as_forall_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let b: Bool = forall(x: Bool, Nat: Bool) { x = x }");
    }

    #[test]
    fn test_reusing_type_name_as_lambda_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let f: (bool, bool) -> Bool = function(x: Bool, Nat: Bool) { x = x }");
    }

    #[test]
    fn test_parsing_true_false_keywords() {
        let mut env = Environment::new_test();
        env.add("let b: Bool = true or false");
    }

    #[test]
    fn test_nothing_after_explicit_false() {
        let mut env = Environment::new_test();
        env.add("let b: Bool = axiom");
        env.bad(
            r#"
            if b = not b {
                false
                b
            }
        "#,
        );
    }

    #[test]
    fn test_condition_must_be_valid() {
        let mut env = Environment::new_test();
        env.bad(
            r#"
            if a {
            }
        "#,
        );
    }

    #[test]
    fn test_inline_function_in_forall_block() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let zero: Nat = axiom");
        env.add("let suc: Nat -> Nat = axiom");
        env.add(
            r#"
            axiom induction(f: Nat -> Bool) {
                f(zero) and forall(k: Nat) { f(k) -> f(suc(k)) } -> forall(n: Nat) { f(n) }
            }
            "#,
        );
        env.add(
            r#"
            forall(f: (Nat, Bool) -> Bool) {
                induction(function(x: Nat) { f(x, true) })
            }
        "#,
        );
    }

    #[test]
    fn test_structs_must_be_capitalized() {
        let mut env = Environment::new_test();
        env.bad(
            r#"
            struct foo {
                bar: Bool
            }
        "#,
        );
    }

    #[test]
    fn test_axiomatic_types_must_be_capitalized() {
        let mut env = Environment::new_test();
        env.bad("type foo: axiom");
    }

    #[test]
    fn test_functional_definition_typechecking() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("define foo(f: Nat -> Nat) -> Bool { function(x: Nat) { true } }");
    }

    #[test]
    fn test_partial_application() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("let zero: Nat = axiom");
        env.add("define add3(a: Nat, b: Nat, c: Nat) -> Nat { axiom }");
        env.add("let add0: (Nat, Nat) -> Nat = add3(zero)");
        env.add("let add00: Nat -> Nat = add3(zero, zero)");
        env.add("let add00_alt: Nat -> Nat = add0(zero)");
    }

    #[test]
    fn test_else_on_new_line() {
        // This is ugly but it should work.
        let mut env = Environment::new_test();
        env.add(
            r#"
        let b: Bool = axiom
        if b {
            b
        }
        else {
            not b
        }
        "#,
        );
    }

    #[test]
    fn test_arg_names_lowercased() {
        let mut env = Environment::new_test();
        env.bad("let f: Bool -> Bool = function(A: Bool) { true }");
        env.add("let f: Bool -> Bool = function(a: Bool) { true }");
        env.bad("forall(A: Bool) { true }");
        env.add("forall(a: Bool) { true }");
        env.bad("define foo(X: Bool) -> Bool { true }");
        env.add("define foo(x: Bool) -> Bool { true }");
        env.bad("theorem bar(X: Bool) { true }");
        env.add("theorem bar(x: Bool) { true }");
    }

    #[test]
    fn test_undefined_class_name() {
        let mut env = Environment::new_test();
        env.bad("class Foo {}");
    }

    #[test]
    fn test_class_variables() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                let zero: Nat = axiom
                let 1: Nat = axiom
            }

            axiom zero_neq_one(x: Nat) { Nat.zero = Nat.1 }
        "#,
        );

        // Class variables shouldn't get bound at module scope
        env.bad("let alsozero: Nat = zero");
    }

    #[test]
    fn test_instance_methods() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define add(self, other: Nat) -> Nat { axiom }
            }
        "#,
        );
    }

    #[test]
    fn test_no_methods_on_type_aliases() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.add("type NatFn: Nat -> Nat");
        env.bad("class NatFn {}");
    }

    #[test]
    fn test_first_arg_must_be_self() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad(
            r#"
            class Nat {
                define add(a: Nat, b: Nat) -> Nat { axiom }
            }
            "#,
        );
    }

    #[test]
    fn test_no_self_variables() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let foo: Bool = exists(self) { true }");
        env.bad("let foo: Bool = forall(self) { true }");
        env.bad("let self: Nat = axiom");
    }

    #[test]
    fn test_no_self_args_outside_class() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("define foo(self) -> Bool { true }");
    }

    #[test]
    fn test_no_self_as_forall_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("forall(self) { true }");
    }

    #[test]
    fn test_no_self_as_exists_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("exists(self) { true }");
    }

    #[test]
    fn test_no_self_as_lambda_arg() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let f: Nat -> Bool = lambda(self) { true }");
    }

    #[test]
    fn test_using_member_function() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define add(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) {
                a.add(b) = b.add(a)
            }
        "#,
        );
    }

    #[test]
    fn test_infix_add() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define add(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a + b = b + a }
        "#,
        );
    }

    #[test]
    fn test_infix_sub() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define sub(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a - b = b - a }
        "#,
        );
    }

    #[test]
    fn test_infix_mul() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define mul(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a * b = b * a }
        "#,
        );
    }

    #[test]
    fn test_infix_div() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define div(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a / b = b / a }
        "#,
        );
    }

    #[test]
    fn test_infix_mod() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define mod(self, other: Nat) -> Nat { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a % b = b % a }
        "#,
        );
    }

    #[test]
    fn test_infix_lt() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define lt(self, other: Nat) -> Bool { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a < b = b < a }
        "#,
        );
    }

    #[test]
    fn test_infix_gt() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define gt(self, other: Nat) -> Bool { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a > b = b > a }
        "#,
        );
    }

    #[test]
    fn test_infix_lte() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define lte(self, other: Nat) -> Bool { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a <= b = b <= a }
        "#,
        );
    }

    #[test]
    fn test_infix_gte() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define gte(self, other: Nat) -> Bool { axiom }
            }
            theorem goal(a: Nat, b: Nat) { a >= b = b >= a }
        "#,
        );
    }

    #[test]
    fn test_self_must_have_correct_type() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad(
            r#"
            class Nat {
                define add(self: Bool, other: Nat) -> Nat { axiom }
            }
        "#,
        );
    }

    #[test]
    fn test_no_dot_new() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            structure NatPair {
                first: Nat
                second: Nat
            }
        "#,
        );
        env.bad("theorem goal(p: NatPair): p.new = p.new");
    }

    #[test]
    fn test_no_defining_new() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad(
            r#"
            class Nat {
                define new(self: Bool, other: Nat) -> Bool { true }
            }
        "#,
        );
    }

    #[test]
    fn test_no_using_methods_with_mismatched_self() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            let zero: Nat = axiom
            class Nat {
                let foo: Bool -> Bool = function(b: Bool) { b }
            }
        "#,
        );
        env.bad("theorem goal: zero.foo(true)");
    }

    #[test]
    fn test_infix_codegen() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                define add(self, other: Nat) -> Nat { axiom }
                define sub(self, other: Nat) -> Nat { axiom }
                define mul(self, other: Nat) -> Nat { axiom }
                define div(self, other: Nat) -> Nat { axiom }
                define mod(self, other: Nat) -> Nat { axiom }
                define lt(self, other: Nat) -> Bool { axiom }
                define gt(self, other: Nat) -> Bool { axiom }
                define lte(self, other: Nat) -> Bool { axiom }
                define gte(self, other: Nat) -> Bool { axiom }
                define suc(self) -> Nat { axiom }
                define foo(self, other: Nat) -> Nat { axiom }
                let 0: Nat = axiom
                let 1: Nat = axiom
            }
            numerals Nat
        "#,
        );
        env.bindings.expect_good_code("0 + 1");
        env.bindings.expect_good_code("0 - 1");
        env.bindings.expect_good_code("0 * 1");
        env.bindings.expect_good_code("0 / 1");
        env.bindings.expect_good_code("0 % 1");
        env.bindings.expect_good_code("0 < 1");
        env.bindings.expect_good_code("0 > 1");
        env.bindings.expect_good_code("0 <= 1");
        env.bindings.expect_good_code("0 >= 1");
        env.bindings.expect_good_code("0 + 0 * 0");
        env.bindings.expect_good_code("(0 + 0) * 0");
        env.bindings.expect_good_code("0 + 0 + 0");
        env.bindings.expect_good_code("1 - (1 - 1)");
        env.bindings.expect_good_code("(0 + 1).suc = 1 + 1");
        env.bindings.expect_good_code("1 + 1 * 1");
        env.bindings.expect_good_code("0.suc = 1");
        env.bindings.expect_good_code("0.foo(1)");
    }

    #[test]
    fn test_no_magic_names_for_constants() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad(
            r#"
            class Nat {
                let add: Nat = axiom
            }
        "#,
        );
    }

    #[test]
    fn test_no_magic_names_for_struct_fields() {
        let mut env = Environment::new_test();
        env.bad(
            r#"
            struct MyStruct {
                add: Bool
            }
        "#,
        );
    }

    #[test]
    fn test_numerals_statement() {
        let mut env = Environment::new_test();
        env.add("type Foo: axiom");
        env.add("numerals Foo");
        env.bad("numerals Bar");
        env.bad("numerals Bool");
        env.bad("numerals Foo -> Foo");
    }

    #[test]
    fn test_no_defining_top_level_numbers() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad("let 0: Nat = axiom");
    }

    #[test]
    fn test_no_top_level_numbers_without_a_numerals() {
        let mut env = Environment::new_test();
        env.bad("let foo: Bool = (0 = 0)");
    }

    #[test]
    fn test_multi_digit_unary() {
        let mut env = Environment::new_test();
        env.add("type Unary: axiom");
        env.add(
            r#"
            class Unary {
                let 1: Unary = axiom 
                define suc(self) -> Unary { axiom }
                define read(self, digit: Unary) -> Unary { self.suc }
            }
        "#,
        );
        env.add("numerals Unary");
        env.add("let two: Unary = 11");
    }

    #[test]
    fn test_digits_must_be_correct_type() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad(
            r#"
            class Nat {
                let 1: Bool = axiom
            }
        "#,
        );
    }

    #[test]
    fn test_read_must_have_correct_args() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad(
            r#"
            class Nat {
                let 1: Nat = axiom
                define suc(self) -> Nat: axiom
                define read(self, digit: Bool) -> Nat: Nat.1
            }
        "#,
        );
    }

    #[test]
    fn test_read_must_return_correct_type() {
        let mut env = Environment::new_test();
        env.add("type Nat: axiom");
        env.bad(
            r#"
            class Nat {
                let 1: Nat = axiom
                define suc(self) -> Nat: axiom
                define read(self, digit: Nat) -> Bool: true
            }
        "#,
        );
    }

    #[test]
    fn test_numeric_literal_codegen() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                let 0: Nat = axiom
                define suc(self) -> Nat { axiom }
                let 1: Nat = Nat.0.suc
                let 2: Nat = Nat.1.suc
                let 3: Nat = Nat.2.suc
                let 4: Nat = Nat.3.suc
                let 5: Nat = Nat.4.suc
                let 6: Nat = Nat.5.suc
                let 7: Nat = Nat.6.suc
                let 8: Nat = Nat.7.suc
                let 9: Nat = Nat.8.suc
                let 10: Nat = Nat.9.suc
                define read(self, other: Nat) -> Nat { axiom }
                define add(self, other: Nat) -> Nat { axiom }
            }
            numerals Nat
        "#,
        );
        env.bindings.expect_good_code("7");
        env.bindings.expect_good_code("10");
        env.bindings.expect_good_code("12");
        env.bindings.expect_good_code("123 + 456");
        env.bindings.expect_good_code("0.suc");
    }

    #[test]
    fn test_non_default_numeric_literals() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            type Nat: axiom
            class Nat {
                let 0: Nat = axiom
                define suc(self) -> Nat { axiom }
                let 1: Nat = Nat.0.suc
                let 2: Nat = Nat.1.suc
                let 3: Nat = Nat.2.suc
                let 4: Nat = Nat.3.suc
                let 5: Nat = Nat.4.suc
                let 6: Nat = Nat.5.suc
                let 7: Nat = Nat.6.suc
                let 8: Nat = Nat.7.suc
                let 9: Nat = Nat.8.suc
                let 10: Nat = Nat.9.suc
                define read(self, other: Nat) -> Nat { axiom }
                define add(self, other: Nat) -> Nat { axiom }
            }
        "#,
        );
        env.bindings.expect_good_code("Nat.7");
        env.bindings.expect_good_code("Nat.10");
        env.bindings.expect_good_code("Nat.12");
        env.bindings.expect_good_code("Nat.123 + Nat.456");
    }

    #[test]
    fn test_root_level_solve() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            let b: Bool = true or false
            solve b by {
                b = true
            }
            "#,
        );
    }

    #[test]
    fn test_nested_solve() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            let b: Bool = true or false
            if b or b {
                solve b by {
                    b = true
                }
            }
            "#,
        );
    }

    #[test]
    fn test_infix_solve() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            let b: Bool = true or false
            solve b or b by {
                b or b = b
            }
            "#,
        );
    }

    #[test]
    fn test_solve_block_has_a_goal_path() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            let b: Bool = true or false
            solve b by {
            }
            "#,
        );
        assert_eq!(env.iter_goals().count(), 1);
    }

    #[test]
    fn test_basic_problem_statement() {
        let mut env = Environment::new_test();
        env.add(
            r#"
            problem {
                let b: Bool = true or false
                solve b by {
                }
            }
            "#,
        );
    }
}
