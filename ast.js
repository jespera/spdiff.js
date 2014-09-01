/**
   We represent ASTs using maps (objects) in a generic manner. Each
   object is assumed to have at least the following two fields:
   
   - "op"; which indicates node-type, and
   - "children"; an array of child nodes and their order (empty for terminal nodes)
 
   representation of the statement "y = 42;"

   { op: "statement"
     children: ["assignExp"]
     assignExp: { op: "exp"
            children: ["assign"]
	    assign: {op: "assign"
	             children: ["lval", "assignOp", "exp"]
		     lval: {op: "id", children: [], value: "y"}
		     assignOp: {op "assignOp" value: "="}
		     exp: {op: "exp", children: ["num"] 


   Alternatively, just use the 'treehugger' library for ASTs?
   https://github.com/ajaxorg/treehugger

   We need to be able to perform the following operations with trees:
   - isAbstraction : ast -> ast -> bindings
   - equals: ast -> ast -> bool
   - antiunify: ast -> ast -> pattern

   "isAbstraction t1 t2" tests whether t1 is an abstraction of t2 and
   returns the smallest binding that can be used to convert t1 into
   t2.

   "equals t1 t2" returns true if the two asts are (syntactically) the
   same.

   To test for alpha-equivalence of t1 and t2, isAbstraction can be
   used twice or one can normalize meta-vars in both t1 and t2 and
   test for equality.

   Ideally, we'd like equality test to be a constant-time operation.

   "antiunfy t1 t2" computes the least general generalization t3 such
   that t3 is an abstraction of both t1 and t2.


**/

var AST = (function(){

    function makeTerm(op, args) {
        return { op: op, args: args};
    }

    function equalsTerm(t1, t2) {
        if (t1.op !== t2.op) {
            return false;
        }
        if (t1.length !== t2.length) {
            return false;
        }
        
        for(var i in t1.args) {
            if(!equalsTerm(t1.args[i], t2.args[i])) {
                return false;
            }
        }
        return true;
    }

    function matches(pattern, tree) {
    }
    
    return {
        mk: makeTerm,
        equals: equalsTerm
    };
})();
