/**


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
	return murmurhash3_32_gc(s, 0);
	// return s.split("").reduce(function(a,b){
	//     a=((a<<5)-a)+b.charCodeAt(0);
	//     return a&a
	// },0);
    }

    var terms = {};

    function isTerm(term) {
	return term && term.op;
    }

    function getHKey(term) {
	if(isTerm(term)) {
	    return term.hkey;
	} else {
	    return hashCode(term);
	}
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
	return term && term.op && term.op === "meta";
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
	return tree1 && tree2
	    && tree1.op === tree2.op 
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
    function mergeTerms(tree1, tree2, startEnv) {
	var env = startEnv || {};
	function merge(t1, t2) {
	    if(equalsTerm(t1, t2)) {
		return isDone(t1);
	    }
	    if(areComparable(t1, t2)) {
		return notDone(t1.op);
	    }
	    var boundMeta = env[[getHKey(t1),getHKey(t2)]];
	    if(boundMeta) {
		return isDone(boundMeta);
	    }
	    
	    var newMeta = makeMeta();
	    env[[getHKey(t1),getHKey(t2)]] = newMeta;
	    
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

    function mergeRewrites(rw1, rw2) {
	var mergeEnv = {};
	var mergedLHS = mergeTerms(rw1.lhs, rw2.lhs, mergeEnv);
	var mergedRHS = mergeTerms(rw1.rhs, rw2.rhs, mergeEnv);
	return mkRewrite(mergedLHS, mergedRHS);
    }
    
    // apply a term-rewrite, lhs=>rhs such that every subterm, sub of
    // tree where computeMatches(lhs,sub) = env and and <> null is
    // replaced by applyPattern(rhs, env)
    function applyRewrite(patch, tree) {
	function apply(tree) {
	    var env = computeMatches(patch.lhs, tree);
	    if(env) {
		return applyPattern(patch.rhs, env);
	    } 
	    if(tree.elems) {
		return makeTerm(tree.op, tree.elems.map(apply));
	    }

	    return tree;
	    
	
	}
	return apply(tree);
    }

    function treeSize(tree) {
	var accSize = 0;
	function size(tree) {
	    if(!tree) { return; }
	    accSize++;
	    if(isTerm(tree) && tree.elems) {
		for(var i in tree.elems) {
		    size(tree.elems[i]);
		}
	    }
	}
	size(tree);
	return accSize;
	
    }

    function eqIs0(l, r) {
	return (equalsTerm(l,r)) ? 0 : 2;
    }

    
    function editDist(oldT, newT) {
	function red(s, t) {
	    return treeSize(t) + s;
	}
	var memoDist = {};
	function distTerms(oldElems, newElems) {
	    if(oldElems.length == 0 && newElems.length > 0) {
		return newElems.reduce(red, 0);
	    }
	    if(newElems.length == 0 && oldElems.length > 0) {
		return oldElems.reduce(red, 0);
	    }
	    if(newElems.length == 0 && oldElems.length == 0) {
		return 0;
	    }
	    // both oldElems and newElems are non-null and have a
	    // length > 0
	    var min1 = 
		distTerms(oldElems.slice(1), 
			  newElems)
		+ treeSize(oldElems[0]);
	    var min2 = 		
		distTerms(oldElems, 
			  newElems.slice(1))
		+ treeSize(newElems[0]);

	    var min3 =
		distTerms(oldElems.slice(1),
			  newElems.slice(1)) 
		+ dist(oldElems[0], 
		       newElems[0]);
	    
	    var res = Math.min(min1,min2,min3);
	    return res;
	}
	
	function dist(o,n) {
	    var ohkey = getHKey(o);
	    var nhkey = getHKey(n);
	    var memoKey = [ohkey, nhkey];
	    var memo = memoDist[memoKey];
	    if(memo) {
		return memo;
	    }
	    var newMemo = 0;
	    var oIsTerm = isTerm(o);
	    var nIsTerm = isTerm(n);
	    if(oIsTerm && nIsTerm){
		if(equalsTerm(o,n)) {
		    newMemo = 0;
		} else {
		    newMemo = eqIs0(o.op, n.op) + distTerms(o.elems, n.elems);
		}
	    } else if(oIsTerm && !nIsTerm) {
		newMemo = 1 + treeSize(o);
	    } else if(!oIsTerm && nIsTerm) {
		newMemo = 1 + treeSize(n);
	    } else {
		newMemo = eqIs0(o, n);
	    }
	    memoDist[memoKey] = newMemo;
	    return newMemo;
	}
	return dist(oldT, newT);
    }

    function print(origTerm) {
	var str = "";
	function toStr(term) {
	    if(isMeta(term)) {
		str += "X" + JSON.stringify(term.elems[0]);
		
	    } else if(isTerm(term)) {
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

    function isSafe(rewrite, srcTerm, tgtTerm) {
	var midTerm = applyRewrite(rewrite, srcTerm);
	return editDist(srcTerm, midTerm) + editDist(midTerm,tgtTerm) === editDist(srcTerm,tgtTerm);
    }


    function diffCost(diff) {
	return diff.reduce(
	    function(accCost, diffElem) {
		return accCost + treeSize(diffElem.lhs) + treeSize(diffElem.rhs);
	    }, 0);
    }

    function d(srcTerms, tgtTerms) {
	/* d([], ys) = map (+) ys
	       d(xs, []) = map (-) xs
	       d(x:xs, y:ys) =
	       let min1 = -x @ d(xs, y:ys)
	       let min2 = +y @ d(x:xs, ys)
		 let min3 = d(x,y) @ d(xs,ys)
		 min_by cost [min1, min2, min3]
	*/
	if(srcTerms.length == 0) {
	    return tgtTerms.map(function(term) {
		    return mkRewrite(null, term);
	    });
	}
	if(tgtTerms.length == 0) {
	    return srcTerms.map(function(term) {
		return mkRewrite(term, null);
	    });
	}
	var min1 = [mkRewrite(srcTerms[0],null)].concat(d(srcTerms.slice(1), tgtTerms));
	var cost1 = diffCost(min1);
	var min2 = [mkRewrite(null, tgtTerms[0])].concat(d(srcTerms, tgtTerms.slice(1)));
	var cost2 = diffCost(min2);
	var min3 = getMinimalDiffs(srcTerms[0],tgtTerms[0]).concat(d(srcTerms.slice(1),tgtTerms.slice(1)));
	var cost3 = diffCost(min3);
	if(cost3 <= cost1 && cost3 <= cost2) {
	    return min3;
	} else if ( cost1 <= cost2) {
	    return min1;
	} else {
	    return min2;
	}
    }
    
    function getMinimalDiffs(srcTerm, tgtTerm) {
	if(equalsTerm(srcTerm, tgtTerm)) {
	    return [];
	}
	if(isTerm(srcTerm) && isTerm(tgtTerm)) {
	    var diffs = [];
	    if(srcTerm.op !== tgtTerm.op) {
		diffs.push(mkRewrite(srcTerm.op, tgtTerm.op));
	    }
	    return diffs.concat(d(srcTerm.elems, tgtTerm.elems));
	}
	return [mkRewrite(srcTerm, tgtTerm)];
    }

    function getSimpleDiffs(srcTerm, tgtTerm) {
	var diffs = [];
	function get(src,tgt) {
	    if(equalsTerm(src,tgt)) {
		return;
	    }
	    diffs.push(mkRewrite(src,tgt));
	    if(src && tgt && src.elems && tgt.elems &&
	       src.elems.length == tgt.elems.length) {
		src.elems.forEach(
		    function(srcElem, srcIndex) {
			var tgtElem = tgt.elems[srcIndex];
			get(srcElem, tgtElem);
		    }
		)
	    }
	}
	get(srcTerm, tgtTerm);
	return diffs;
    }

    // we'll assume both lhsRewrite and rhsRewrite are safe for the changeset given
    // in other words, both rewrites applies to all pairs in the changeset 
    function isSubRewrite(changeset) { // changeset = [ {oldTerm:term,newTerm:term} ]
	return function(lhsRewrite, rhsRewrite) {
	    return changeset.every(function(change) {
		var midTerm = applyRewrite(rhsRewrite(change.newTerm));
		return isSafe(lhsRewrite, change.oldTerm, midTerm);
	    });
	}
    }
    
    // given changeset:
    // map each changeset to set of simple changes
    // try to merge simple changes from all elements in changeset
    // - remove merged change if unsafe
    // - don't merge with more changes if merged change is subpatch of already found

    function getMergeDiffs(changeset) {
	var simpleDiffs = changeset.map(function(change) {
	    return getSimpleDiffs(change.oldTerm, change.newTerm);
	});
	var mergedChanges = [];
	function mergeFold(curMerge, otherDiffs) {
	    if(otherDiffs.length == 0) {
		mergedChanges.push(curMerge);
	    } else {
		var rewrites = otherDiffs[0];
		rewrites.forEach(function (rewrite) {
		    var newMerge = curMerge ? mergeRewrites(curMerge, rewrite) : rewrite;
		    // todo
		    // check safety
		    var newMergeSafe = changeset.every(function(change) {
			return isSafe(newMerge, change.oldTerm, change.newTerm);
		    });
		    if(!newMergeSafe) {
			return;
		    }
		    	
		    // check not subpatch of already found patch
		    // maybe not?
		    mergeFold(newMerge, otherDiffs.slice(1));
		});
	    }
	}
	mergeFold(null, simpleDiffs);
	// filter out found changes that are not smalles (unless we do that in the "base-case"
	return mergedChanges;
    }
    
    function printRewrite(rw) {
	return print(rw.lhs) + " => " + print(rw.rhs);
    }
    
    return {
        mk: makeTerm,
	mkRewrite: mkRewrite,
        equals: equalsTerm,
	applyPattern: applyPattern,
	mergeTerms: mergeTerms,
	computeMatches: computeMatches,
	applyRewrite: applyRewrite,
	isSafe: isSafe,
	print: print,
	size: treeSize,
	dist: editDist,
	rewrites: getSimpleDiffs,
	mergeRewrites: mergeRewrites,
	printRewrite: printRewrite,
	getMergeDiffs: getMergeDiffs
    };
})();

var term1 = AST.mk("num", [42]);
var term2 = AST.mk("num", [117]);
var term3 = AST.mk("num", [10]);
var termf = AST.mk("id",["f"]);

var f1 = AST.mk("call", [termf, term1, term1]);
var f2 = AST.mk("call", [termf, term2, term1]);

var f3 = AST.mk("call", [termf, term1, term2]);
var f4 = AST.mk("call", [termf, term2, term2]);

var changeset = [{oldTerm: f1, newTerm: f2}, {oldTerm: f3, newTerm: f4}];

var rw1 = { lhs: f1, rhs: f2 }
var rw2 = { lhs: f3, rhs: f4 }

//console.log("mergedrewrite: " + JSON.stringify(AST.mergeRewrites(rw1, rw2),null,2));
console.log("result: ");
var rewrites = AST.getMergeDiffs(changeset); 
console.log("rewrites:");
if(rewrites) {
    rewrites.forEach(function(rewrite) {
	console.log("::: " + AST.printRewrite(rewrite));
    });
} else {
    console.log("null rewrites?");
}

//console.log(JSON.stringify(newTerm,null,2));

/*
  TODO

  - make tree traversal more generic so we don't rely on concrete
    implementation externally

  - modularize into several modules; patterns do not belong in AST

  - write tests
*/
//AST.mergeTerms(f1,f1)
