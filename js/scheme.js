// A Scheme keeps track of which theorems prove various category-level
// invariants, and is used by a Proof to manipulate terms in a proof
// tree.
//
// Under a particular Scheme, each kind has a particular operator that
// serves as its "natural arrow", taking two inputs of that kind
// and outputing a wff.  The "natural equivalence" is then defined as a
// natural arrow going in both directions.  (Typically these arrows
// are -> for wff, <= for num, and C_ for sets.)
// TODO: is transitivity required for these arrows?
//
// Also, each operator has a "binding" for each of its inputs, which
// determines how the proof-tree can be automatically manipulated.
// Their squishy meanings are:
// - Right:   this input can be replaced with anything that arrows it
// - Left:    this input can be replaced with anything that it arrows
// - Exact:   this input can be replaced with anything it is equivalent to
// - Alpha:   this input is the argument of a quantifier, and changing it
//            requires an alpha transform.
// - Unknown:this input cannot be changed.  This is the default.
//
// TODO: support/document initial and terminal elements

// @param wffArrow: the natural operator of wff, which ought to be ->.
// @param modusPonens: the name of the inference ((A (-> A B)) B).
exports.Scheme = function(wffArrow, modusPonens) {
    var scheme = this;
    // Binding enumeration.  As an implementation detail, we assign
    // each binding a float, since composition is then just multiplication
    // (with the exception of Infinity * 0 = Infinity instead of NaN).
    // Bindings are immutable but may only be compared with their equals().
    function Binding(f) {
        this.f = function() { return f;};
        this.isUnknown = function() {
            return (!isNaN(f) && !isFinite(f));
        };
        this.isAlpha = function() {
            return isNaN(f);
        };
        this.compose = function(childBinding) {
            if (this.isUnknown()) {
                return scheme.UNKNOWN();
            }
            return new Binding(this.f() * childBinding.f());
        };
        this.toString = function() {
            if (f == 0)   return "exact";
            if (f == 1)   return "left";
            if (f == -1)  return "right";
            if (isNaN(f)) return "alpha";
            return "unknown";
        };
        this.equals = function(otherBinding) {
            if (this.isUnknown()) return otherBinding.isUnknown();
            if (this.isAlpha()) return otherBinding.isAlpha();
            return this.f() == otherBinding.f();
        };
    }

    // maps kind to arrow
    var arrows = {  };
    // maps kind to {operator, theorem1, theorem2}
    var equivalences = { };
    // maps operator x argIndex to {binding, theorem}
    var bindings = { };

    arrows[wffArrow.input(0)] = wffArrow;

    // ================ Public Methods ================
    this.LEFT = function() { return new Binding(1); };
    this.RIGHT = function() { return new Binding(-1); };
    this.EXACT = function() { return new Binding(0); };
    this.ALPHA = function() { return new Binding(NaN); };
    this.UNKNOWN = function() { return new Binding(Infinity); };

    this.setArrow = function(kind, operator) {
        arrows[kind] = operator;
    };
    this.getArrow = function(kind) {
        return arrows[kind];
    };

    // @param theorem1 the name of the theorem (-> (operator A B) (arrow A B))
    // @param theorem2 the name of the theorem (-> (operator A B) (arrow B A))
    this.setEquivalence = function(kind, operator, theorem1, theorem2) {
        equivalences[kind] = {operator:operator, theorem1: theorem1, theorem2: theorem2};
    };
    this.getEquivalence = function(kind) {
        if (!equivalences[kind]) return null;
        return equivalences[kind].operator;
    };

    // @param theoremName the name of the theorem that proves the
    // appropriate transformation for this binding.
    this.setBinding = function(operator, argIndex, binding, theoremName) {
        if (!(binding instanceof Binding)) throw new Error("Bad binding " + binding);
        if ((argIndex < 0) || (argIndex >= operator.arity())) {
            throw new Error("Bad argIndex" + argIndex);
        }
        if (!bindings[operator]) bindings[operator] = [];
        bindings[operator][argIndex] = {binding: binding, theorem: theoremName};
    };
    this.getBinding = function(operator, argIndex) {
        if (!bindings[operator] || !bindings[operator][argIndex]) return this.UNKNOWN();
        return bindings[operator][argIndex].binding;
    };
    this.getTheorem = function(operator, argIndex) {
        if (!bindings[operator] || !bindings[operator][argIndex]) {
            throw new Error("no binding theorem for " + operator + "." + argIndex);
        }
        return bindings[operator][argIndex].theorem;
    };
    this.modusPonens = function(direction) {
        //TODO: direction
        return modusPonens;
    };
};
