'use strict';

var murmurHash3 = require("murmurhash3js");
var jsParser = require('recast')
//var jsParser = require('acorn');

function str(obj) {
		return JSON.stringify(obj,null,2);
}

function hashCode(s){
		var valueToHash =
			!s.split ? "\"" + s.toString() + "\"" : s;
				// we don't want numbers and and their string representation
				// to hash to the same value
		return murmurHash3.x86.hash32(valueToHash);
		// return s.split("").reduce(function(a,b){
		//     a=((a<<5)-a)+b.charCodeAt(0);
		//     return a&a
		// },0);
}

var termsMemo = {};

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
		if(!Array.isArray(elems)) {
				console.log("something is wrong with elems: " + JSON.stringify(elems,null,2))
				throw "Oh no!";
		}
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
		var existingTerm = termsMemo[termHash];
		if(existingTerm){
				//TODO: handle collisions
				return existingTerm;
		}
    var newTerm = { op: op, elems: elems, hkey: termHash};
		//TODO: somehow get weak references here
		termsMemo[termHash] = newTerm;
		return newTerm;
}

var nextMeta = 0;

function makeMeta() {
		var m = nextMeta;
		nextMeta = nextMeta + 1;
		return makeTerm("meta", [m]);
}

function makeMetaAt(num) {
	return makeTerm("meta", [num]);
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
		return sub[meta.hkey];
}

// updates 'sub' to have a binding from 'meta' to 'term'
function bindTerm(meta,term,sub){
		sub[meta.hkey] = term;
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
				if(equalsTerm(pattern, tree)) {
						return;
				}
				if(isMeta(pattern)) {
						var boundTerm = lookupMeta(pattern, env);
						if(typeof boundTerm === "undefined" || boundTerm == null) {
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
				if(typeof boundMeta !== undefined && boundMeta != null) {
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

function getMetas(t) {
	var metas = [];
	function loop(t) {
		if(isMeta(t)) {
			metas.push(t);
		} else {
			if(t && t.op && t.elems.length > 0) {
				t.elems.forEach(loop);
			}
 		}
	}
	loop(t);
	return metas;
}

function metaReplace(rewrite, term) {
	if(equalsTerm(rewrite.lhs, term)) {
		return rewrite.rhs;
	}
	if(isTerm(term)) {
		return makeTerm(term.op, term.elems.map(function(t) {
			return metaReplace(rewrite, t);
		}));
	} else {
		return term;
	}
}

function mergeRewrites(rw1, rw2) {
		var mergeEnv = {};

		var mergedLHS = mergeTerms(rw1.lhs, rw2.lhs, mergeEnv);
		var mergedRHS = mergeTerms(rw1.rhs, rw2.rhs, mergeEnv);
		var lhsMetas = getMetas(mergedLHS);
		var rhsMetas = getMetas(mergedRHS);
		var unboundMetas =
			rhsMetas.filter(function (rhsMeta) {
				return lhsMetas.every(function(lhsMeta) {
					return !equalsTerm(lhsMeta, rhsMeta);
				})
			});
		if(unboundMetas.length == 0) {
			return mkRewrite(mergedLHS, mergedRHS);
		} else {
			// some RHS meta is unbound
			// console.log("some unbound metas for " + print(mergedLHS) + " => " + print(mergedRHS));
			// for each unbound meta:
			var resultRHS = mergedRHS;
			unboundMetas.forEach(function (meta) {
				for(var key in mergeEnv) {
					var thisMeta = mergeEnv[key];
					if(equalsTerm(mergeEnv[key], meta)) {
						var hkeys = key.split(",");
						var left = hkeys[0];
						var right = hkeys[1];
						for(var otherKey in mergeEnv) {
							var oMeta = mergeEnv[otherKey];
							// console.log("mergeEnv[otherKey] = " + str(oMeta));
							var otherHKeys = otherKey.split(",");
							var otherLeft = otherHKeys[0];
							var otherRight = otherHKeys[1];
							if(otherLeft === left && otherRight !== right ||
								 otherRight === right && otherLeft !== left) {
								// console.log("other: " + str(otherKey));
								// console.log("this : " + str(key));
								// console.log("mergeEnv " + str(mergeEnv));
								// console.log("apply rewrite: " + printRewrite(mkRewrite(meta, oMeta)));
								// console.log("to : " + print(resultRHS));
								resultRHS = metaReplace(mkRewrite(meta, oMeta), resultRHS);
								// console.log("resultRHS: " + print(resultRHS));
								return;
							}
						}
					}
				}
			});
			return mkRewrite(mergedLHS, resultRHS);
			// - find the pair of terms it was bound to in mergeEnv
			// - try to find another pair such that one equals one from the previous pair
			// - get the meta the new pair binds to and replace old meta with newly found
		}
}

// apply a term-rewrite, lhs=>rhs such that every subterm, sub of
// tree where computeMatches(lhs,sub) = env and and <> null is
// replaced by applyPattern(rhs, env)
function applyRewrite(patch, origTree) {
		function apply(tree) {
				var env = computeMatches(patch.lhs, tree);
				if(env !== null && env) {
						return applyPattern(patch.rhs, env);
				}
				if(tree.elems) {
						return makeTerm(tree.op, tree.elems.map(apply));
				}

				return tree;


		}
		return apply(origTree);
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
		if(equalsTerm(srcTerm, midTerm)) {
				return false;
		}
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
				} else if ( src && tgt && src.elems && tgt.elems &&
					          src.op === tgt.op &&
                    src.elems.length != tgt.elems.length ) {

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
						var midTerm = applyRewrite(rhsRewrite, change.oldTerm);
						return isSafe(lhsRewrite, change.oldTerm, midTerm);
				});
		}
}

function isUndef(o) {
		return typeof o === "undefined" || o === null;
}

function getSubTerms(term) {
		var subtermSet = {};
		function loop(nextTerm) {
				if(isUndef(nextTerm)) {
						return;
				}
				var key;
				if(isTerm(nextTerm)){
						key = getHKey(nextTerm);
						if(nextTerm.elems) {
								nextTerm.elems.forEach(loop);
						}
				} else if(!isUndef(nextTerm)) {
						key = hashCode(nextTerm);
				}
				if(isUndef(subtermSet[key])) {
						subtermSet[key] = nextTerm;
				}
		}

		loop(term);

		var subterms = [];
		for(var key in subtermSet) {
				if(subtermSet.hasOwnProperty(key)) {
						subterms.push(subtermSet[key]);
				}
		}
		return subterms;
}

function getCommonPatterns(lhss) {
		// a list of lists of subterms
		var subtermLists = lhss.map(getSubTerms);
		var common = [];
		function loop(curPat, subtermListsTail) {
				if(subtermListsTail.length === 0) {
						// TODO
						// - check for existance in list
						// - check infeasible pattern
						common.push(curPat);
				} else {
						var headTerms = subtermListsTail[0];
						headTerms.forEach(function(term){
								var newPat = curPat ? mergeTerms(curPat, term) : term;
								if(isMeta(newPat)) {
										return;
								}
								loop(newPat, subtermListsTail.slice(1));
						});
				}
		}
		loop(null, subtermLists);
		return common;
}

function find(pred, ls) {
	for(var ix in ls) {
		if(pred(ls[ix])) {
			return ls[ix];
		}
	}
}

// given changeset:
// map each changeset to set of simple changes
// try to merge simple changes from all elements in changeset
// - remove merged change if unsafe
// - don't merge with more changes if merged change is subpatch of already found

function getMergeDiffs(changeset) {
		var lhss = changeset.map(function(pair) { return pair.oldTerm; });
		var commonPats = getCommonPatterns(lhss);
		// commonPats.forEach(function(pat) {
		// 		console.log(">>> " + print(pat));
		// });
		console.log("computing pair diffs");
		var simpleDiffs = changeset.map(function(change) {
				// somewhat slow
				return getSimpleDiffs(change.oldTerm, change.newTerm)
        //return getMinimalDiffs(change.oldTerm, change.newTerm)
						.filter(function(change) {
							// console.log("testing simple: " + printRewrite(change));
							var isGood = commonPats.some(function(pat) {
										return computeMatches(pat, change.lhs);
								});
							// console.log(" good? " + isGood);
							return isGood;
						});

				// faster, but fewer results
				//return getMinimalDiffs(change.oldTerm, change.newTerm);
		});

		console.log("no simple diffs = " + simpleDiffs.reduce(function(accSum, diffs) {
			return diffs.length + accSum;
			}, 0));
		// simpleDiffs.forEach(function(diffs) {
		// 	diffs.forEach(function (diff) {
		// 		console.log("diff: " + printRewrite(diff));
		// 	});
		// });
		var mergedChanges = [];

		function mergeFold(curMerge, otherDiffs) {
				if(otherDiffs.length == 0) {
						// check safety
						var newMergeSafe = changeset.every(function(change) {
								return isSafe(curMerge, change.oldTerm, change.newTerm);
						});
						if(!newMergeSafe) {
							return;
						}

						mergedChanges.push(curMerge);
				} else {
						var rewrites = otherDiffs[0];
						rewrites.forEach(function (rewrite) {
								var newMerge = curMerge ? mergeRewrites(curMerge, rewrite) : rewrite;
								if(!newMerge) {
									return;
								}
								if(newMerge && newMerge.lhs && isMeta(newMerge.lhs)) {
										return;
								}
								// TODO: consider to check not subpatch of already found patch
								mergeFold(newMerge, otherDiffs.slice(1));
						});
				}
		}
		console.log("merging diffs");
		mergeFold(null, simpleDiffs);
		// filter out found changes that are not smallest (unless we do that in the "base-case"

		var subPatch = isSubRewrite(changeset);

		var largestChanges =
			mergedChanges.filter(function (patch) {
					return mergedChanges.every(function(other) {
						return subPatch(other, patch);
			})
		});
			// find(function(patch) {
			// 	return mergedChanges.every(function(other) {
			// 		return subPatch(other, patch);
			// 	});
			// }, mergedChanges);

		return largestChanges;
		//return mergedChanges;
}

function printRewrite(rw) {
		return print(rw.lhs) + " => " + print(rw.rhs);
}

function convertToTerm(ast) {
    if(typeof ast === "undefined" || ast == null) {
				throw "No AST?";
    }
    if(typeof(ast) !== "object") {
				return ast;
    }
    if(Array.isArray(ast)){
				return ast.map(convertToTerm);
    }
    if(ast.type) {
				var elems = []
				for(var prop in ast) {
						if(prop !== "type" && prop !== "loc" && prop !== "start" && prop !== "end" && prop !== 'typeAnnotation') {
								if(ast.hasOwnProperty(prop)){
										var value = ast[prop];
										if(value == null) {
												continue;
										}
                    // foo : [a,b,c] => t(foo,[t("[]", [|a|,|b|,|c|]])
										if(Array.isArray(value)) {
												var arr = value.map(convertToTerm);
												elems.push(makeTerm(prop, [makeTerm("[]", arr)]));
										} else {
												var conv = convertToTerm(value);
                        // foo : e => t(foo,[e])
												elems.push(makeTerm(prop, [conv]));
										}

								}
						}
				}
				return makeTerm(ast.type, elems);
    }
    return ast;
}

function convertToAST(term) {
    if(term == null) {
			console.log("no term");
			console.log(term);
        throw "No term?";
    }
    if(typeof(term) !== "object") {
        return term;
    }
    if(Array.isArray(term)) {
        return term.map(convertToAST);
    }
    if(isTerm(term)) {
        if(term.op === "[]") {
            return convertToAST(term.elems);
        }

        if(isMeta(term)) {
						return "X" + term.elems[0];
				}

        var ast = {};
        ast["type"] = term.op;
				if(term.elems.length === 1 && term.elems[0].op === "[]") {
						return convertToAST(term.elems[0]);
				}

        for(var elemIdx in term.elems) {

            var termValue = term.elems[elemIdx];

            var prop = termValue.op;
            if(termValue.elems.length !== 1) {
							// console.log("not === 1");
							// console.log(termValue);
							// console.log(">>> IN :");
							// console.log(term);
              // throw "Not === 1";
							ast[prop] = convertToAST(termValue.elems);
            } else {
							ast[prop] = convertToAST(termValue.elems[0]);
						}
            // if(termValue.elems.length === 0) {
              //  throw "=== 0?";
            // }
        }
        return ast;
    }
    return term;
}

var spdiff = {};

spdiff.applyRewrite = function(rewrite, srcAst) {
	return convertToAST(applyRewrite(rewrite, convertToTerm));
}

spdiff.findLargestCommonRewrites = function(changeset) {
	function convert(change) {
			var oldAST = jsParser.parse(change.oldTerm);
			var newAST = jsParser.parse(change.newTerm);
			return { oldTerm: convertToTerm(oldAST),
							 newTerm: convertToTerm(newAST) };
	}
	var convChangeSet = changeset.map(convert);
	var termRewrites = getMergeDiffs(convChangeSet);

	return termRewrites.map(function (rewrite) {
		try {
			return mkRewrite( convertToAST(rewrite.lhs),
			                  convertToAST(rewrite.rhs) );
		} catch (err) {

		}
	}).filter(function (e) { return e;});
}

spdiff.jsParser = jsParser;

module.exports = spdiff
