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

    function makeTerm(op, elems) {
        return { op: op, elems: elems};
    }

    var nextMeta = 0;

    function makeMeta() {
	var m = nextMeta;
	nextMeta = nextMeta + 1;
	return makeTerm("meta", [m]);
    }

    function isMeta(term) {
	return term.op && term.op === "meta";
    } 

    function isTerm(term) {
	return term.op;
    }

    function equalsTerm(t1, t2) {
	if(!isTerm(t1) || !isTerm(t2)) {
	    return t1 === t2;
	}
        if (t1.op !== t2.op) {
            return false;
        }
        if (t1.length !== t2.length) {
            return false;
        }
        
        for(var i in t1.elems) {
            if(!equalsTerm(t1.elems[i], t2.elems[i])) {
                return false;
            }
        }
        return true;
    }

    // lookup 'meta' in 'sub'
    function lookupMeta(meta, sub) {
	return sub[meta.elems[0]];
    }

    // updates 'sub' to have a binding from 'meta' to 'term'
    function bindTerm(meta,term,sub){
	sub[meta.elems[0]] = term;
    }

    // Apply substitution in 'pattern' with bindings from 'sub'
    function applyPattern(pattern, sub) {
	function apply(pattern) {
	    if(isMeta(pattern)) {
		var boundTerm = sub[pattern.elems[0]];
		if(boundTerm) {
		    return boundTerm;
		}
		return pattern;
	    }
	    if(pattern.elems) {
		var newArgs = pattern.elems.map(apply);
		return makeTerm(pattern.op, newArgs);
	    }
	    return pattern;
	}
	return apply(pattern);
    }

    function areComparable(tree1, tree2) {
	return tree1.op === tree2.op 
	       && tree1.elems && tree2.elems 
	       && tree1.elems.length === tree2.elems.length
    }

    // Compute a substitution from meta-variables in 'pattern' such that
    // applyPattern pattern subst = tree 
    function computeMatches(pattern, tree) {
	var env = {};
	function match(pattern, tree) {
	    if(pattern === tree) {
		return;
	    }
	    if(isMeta(pattern)) {
		var boundTerm = lookupMeta(pattern, env);
		if(!boundTerm) {
		    bindTerm(pattern, tree, env);
		    return;
		}
		if(equalsTerm(boundTerm, tree) ) {
		    return;
		} else {
		    env = null;
		    return;
		}
	    }

	    // pattern is comparable to tree, recurse on each subtree
	    // pattern is non-comparable, fail
	    if(areComparable(pattern, tree) ) 
	    {
		for(var i in pattern.elems) {
		    match(pattern.elems[i], tree.elems[i]);
		    if(!env) {
			return;
		    }
		}
	    } else {
		env = null;
		return;
	    }
	}

	match(pattern, tree);
	return env;
    }
    

    // traverses two trees in parallel, while constructing a
    // aux. value
    function reduce2(tree1, tree2, nodeFun, aux) {
	
    }
    
    // traverses two trees in parallel, while building a new tree
    function traverse2(tree1, tree2, nodeVisit) {
    }
    
    // compute anti-unifier
    function mergeTerms(tree1, tree2) {
	var env = {};
	function merge(t1, t2) {
	    if(equalsTerm(t1, t2)) {
		return t1;
	    }
	    if(areComparable(t1, t2)) {
		var newElems = [];
		for(var i in t1.elems) {
		    newElems.push(merge(t1.elems[i], t2.elems[i]));
		}
		return makeTerm(t1.op, newElems);
	    }
	    var boundMeta = env[[t1,t2]];
	    if(boundMeta) {
		return boundMeta;
	    }
	    var newMeta = makeMeta();
	    env[[t1,t2]] = newMeta;
	    return newMeta;
	}
	
	var merged = merge(tree1, tree2);
	return merged;
    }
    
    function mkRewrite(lhs, rhs) {
	var rewrite = {};
	rewrite.lhs = lhs;
	rewrite.rhs = rhs;
	return rewrite;
    }

    // apply a term-rewrite, lhs=>rhs such that every subterm, sub of
    // tree where computeMatches(lhs,sub) = env and and <> null is
    // replaced by applyPattern(rhs, env)
    function applyRewrite(patch, tree) {
	function apply(tree) {
	    var env = computeMatches(patch.lhs, tree);
	    if(env) {
		return applyPattern(patch.rhs, env);
	    } else if(tree.elems) {
		return makeTerm(tree.op, tree.elems.map(apply));
	    }
	
	}
	return apply(tree);
    }
    
    return {
        mk: makeTerm,
	mkRewrite: mkRewrite,
        equals: equalsTerm,
	applyPattern: applyPattern,
	mergeTerms: mergeTerms,
	computeMatches: computeMatches,
	applyRewrite: applyRewrite
    };
})();

var term1 = AST.mk("num", [42]);
var term2 = AST.mk("num", [117]);
var meta1 = AST.mk("meta", [0]);
var meta2 = AST.mk("meta", [1]);
// f(<meta-1>) {meta-1 : "1"} = f(1)
var test1 = AST.applyPattern(AST.mk("call",[AST.mk("id",["f"]), AST.mk("argList",[{op:"meta",elems:[1]}])]), {1:term1});
var f1 = AST.mk("call", [AST.mk("id",["f"]), term1, term2]);
var f2 = AST.mk("call", [AST.mk("id",["f"]), term1, term1]);
var p1 = AST.mk("call", [AST.mk("id",["f"]), meta1, meta2]);
var p2 = AST.mk("replaced",[meta1, meta2]);
var fplusf = AST.mk("plus",[f1,f2]);
var patch1 = AST.mkRewrite(p1, p2);
//var test1res = AST.equals(test1, f1)

console.log(AST.computeMatches(p1, f1));
//var merged = AST.mergeTerms(f1,f2);
var newTerm = AST.applyRewrite(patch1, fplusf);
console.log(JSON.stringify(newTerm, null, 2));
console.log("equals");
console.log(AST.equals(fplusf, newTerm));
console.log("done");
/*
  TODO

  - implement hash-consing for terms for constant time equality checks

  - make tree traversal more generic so we don't rely on concrete
    implementation externally

  - modularize into several modules; patterns do not belong in AST

  - write tests
*/
AST.mergeTerms(f1,f1)
