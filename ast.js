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

    /**
     * JS Implementation of MurmurHash3 (r136) (as of May 20, 2011)
     * 
     * @author <a href="mailto:gary.court@gmail.com">Gary Court</a>
     * @see http://github.com/garycourt/murmurhash-js
     * @author <a href="mailto:aappleby@gmail.com">Austin Appleby</a>
     * @see http://sites.google.com/site/murmurhash/
     * 
     * @param {string} key ASCII only
     * @param {number} seed Positive integer only
     * @return {number} 32-bit positive integer hash 
     */
    function murmurhash3_32_gc(key, seed) {
	var remainder, bytes, h1, h1b, c1, c1b, c2, c2b, k1, i;
	
	remainder = key.length & 3; // key.length % 4
	bytes = key.length - remainder;
	h1 = seed;
	c1 = 0xcc9e2d51;
	c2 = 0x1b873593;
	i = 0;
	
	while (i < bytes) {
	    k1 = 
	  	((key.charCodeAt(i) & 0xff)) |
	  	((key.charCodeAt(++i) & 0xff) << 8) |
	  	((key.charCodeAt(++i) & 0xff) << 16) |
	  	((key.charCodeAt(++i) & 0xff) << 24);
	    ++i;
	    
	    k1 = ((((k1 & 0xffff) * c1) + ((((k1 >>> 16) * c1) & 0xffff) << 16))) & 0xffffffff;
	    k1 = (k1 << 15) | (k1 >>> 17);
	    k1 = ((((k1 & 0xffff) * c2) + ((((k1 >>> 16) * c2) & 0xffff) << 16))) & 0xffffffff;

	    h1 ^= k1;
            h1 = (h1 << 13) | (h1 >>> 19);
	    h1b = ((((h1 & 0xffff) * 5) + ((((h1 >>> 16) * 5) & 0xffff) << 16))) & 0xffffffff;
	    h1 = (((h1b & 0xffff) + 0x6b64) + ((((h1b >>> 16) + 0xe654) & 0xffff) << 16));
	}
	
	k1 = 0;
	
	switch (remainder) {
	case 3: k1 ^= (key.charCodeAt(i + 2) & 0xff) << 16;
	case 2: k1 ^= (key.charCodeAt(i + 1) & 0xff) << 8;
	case 1: k1 ^= (key.charCodeAt(i) & 0xff);
	    
	    k1 = (((k1 & 0xffff) * c1) + ((((k1 >>> 16) * c1) & 0xffff) << 16)) & 0xffffffff;
	    k1 = (k1 << 15) | (k1 >>> 17);
	    k1 = (((k1 & 0xffff) * c2) + ((((k1 >>> 16) * c2) & 0xffff) << 16)) & 0xffffffff;
	    h1 ^= k1;
	}
	
	h1 ^= key.length;

	h1 ^= h1 >>> 16;
	h1 = (((h1 & 0xffff) * 0x85ebca6b) + ((((h1 >>> 16) * 0x85ebca6b) & 0xffff) << 16)) & 0xffffffff;
	h1 ^= h1 >>> 13;
	h1 = ((((h1 & 0xffff) * 0xc2b2ae35) + ((((h1 >>> 16) * 0xc2b2ae35) & 0xffff) << 16))) & 0xffffffff;
	h1 ^= h1 >>> 16;

	return h1 >>> 0;
    }

    function hashCode(s){
	if(!s.split) {
	    s = s.toString();
	}
	return murmurhash3_32_gc(s, 130);
	// return s.split("").reduce(function(a,b){
	//     a=((a<<5)-a)+b.charCodeAt(0);
	//     return a&a
	// },0);
    }

    var terms = {};

    function isTerm(term) {
	return term.op;
    }

    function makeTerm(op, elems) {
	var opHash = hashCode(op);
	var termHash = 
	    elems.reduce(function(accHash, elem){
		var elemHash;
		if(isTerm(elem)) {
		    elemHash = elem.hkey;
		} else {
		    elemHash = hashCode(elem);
		}
		var newHash = ((accHash<<5)-accHash)+elemHash;
		return Math.abs(newHash & newHash);
	    }, opHash);
	var existingTerm = terms[termHash];
	if(existingTerm){
	    //TODO: handle collisions
	    return existingTerm;
	}
        var newTerm = { op: op, elems: elems, hkey: termHash};
	//TODO: somehow get weak references here
	terms[termHash] = newTerm; 
	return newTerm;
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

    function equalsTerm(t1, t2) {
	if(!isTerm(t1) || !isTerm(t2)) {
	    return t1 === t2;
	}
	return t1.hkey === t2.hkey;
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
		var boundTerm = lookupMeta(pattern, sub);
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
    
    // traverses two trees in parallel, while building a new tree
    function traverse2(nodeVisit) {
	return function visit(tree1, tree2) {
	    var res = nodeVisit(tree1, tree2);
	    if(res.done) {
		return res.newTree;
	    } else if(areComparable(tree1, tree2)){
		var newOp = res.newOp;
		var newElems = [];
		for(var i in tree1.elems){
		    newElems.push(visit(tree1.elems[i],tree2.elems[i]));
		}
		return makeTerm(newOp, newElems);
	    }
	}
    }

    function isDone(newTree) {
	return { done: true,
		 newTree: newTree };
    }

    function notDone(newOp) {
	return { done: false,
		 newOp: newOp };
    }
    
    // compute anti-unifier
    function mergeTerms(tree1, tree2) {
	var env = {};
	function merge(t1, t2) {
	    if(equalsTerm(t1, t2)) {
		return isDone(t1);
	    }
	    if(areComparable(t1, t2)) {
		return notDone(t1.op);
	    }
	    var boundMeta = env[[t1,t2]];
	    if(boundMeta) {
		return isDone(boundMeta);
	    }
	    
	    var newMeta = makeMeta();
	    env[[t1,t2]] = newMeta;
	    
	    return isDone(newMeta);
	}
	
	var visitor = traverse2(merge);
	return visitor(tree1, tree2);
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

    function print(origTerm) {
	var str = "";
	function toStr(term) {
	    if(isTerm(term)) {
		str += term.op;
		if(term.elems && term.elems.length > 0) {
		    str += "(";
		    for(var i in term.elems) {
			toStr(term.elems[i]);
			if(i < term.elems.length - 1) {
			    str += ", ";
			}
		    }
		    str += ")"; 
		}
	    } else {
		str += JSON.stringify(term);
	    }
	    
	}
	toStr(origTerm);
	return str;
    }

    
    return {
        mk: makeTerm,
	mkRewrite: mkRewrite,
        equals: equalsTerm,
	applyPattern: applyPattern,
	mergeTerms: mergeTerms,
	computeMatches: computeMatches,
	applyRewrite: applyRewrite,
	print: print
    };
})();

var term1 = AST.mk("num", [42]);
var term2 = AST.mk("num", [117]);
var meta1 = AST.mk("meta", [0]);
var meta2 = AST.mk("meta", [1]);
// f(<meta-1>) {meta-1 : "1"} = f(1)
var test1 = AST.applyPattern(AST.mk("call",[AST.mk("id",["f"]), AST.mk("argList",[{op:"meta",elems:[1]}])]), {1:term1});
var f1 = AST.mk("call", [AST.mk("id",["f"]), term1, term2]);
var f2 = AST.mk("call", [AST.mk("id",["f"]), term2, term1]);
var p1 = AST.mk("call", [AST.mk("id",["f"]), meta1, meta2]);
var p2 = AST.mk("replaced",[meta1, meta2]);
var fplusf = AST.mk("plus",[f1,f2]);
var patch1 = AST.mkRewrite(p1, p2);
//var test1res = AST.equals(test1, f1)
console.log(f1);
console.log(AST.print(f1));
//console.log(AST.computeMatches(p1, f1));
//var newTerm = AST.mergeTerms(f1,f2);
//var newTerm = AST.applyRewrite(patch1, fplusf);
//console.log(JSON.stringify(newTerm, null, 2));
//console.log("equals");
//console.log(AST.equals(fplusf, newTerm));
//console.log("done");
/*
  TODO

  - implement hash-consing for terms for constant time equality checks

  - make tree traversal more generic so we don't rely on concrete
    implementation externally

  - modularize into several modules; patterns do not belong in AST

  - write tests
*/
//AST.mergeTerms(f1,f1)
