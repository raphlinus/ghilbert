// Copyright 2013 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Computation of deltas based on lines

function cheap_hash(str) {
	var len = str.length;
	if (len === 0) {
		return 0;
	} else if (len === 1) {
		return str.charCodeAt(0);
	} else {
		var half = len >> 1;
		var hash = str.charCodeAt(0) | 0;
		var hash = ((hash << 5) - hash | 0) + str.charCodeAt(len >> 2) | 0;
		var hash = ((hash << 5) - hash | 0) + str.charCodeAt(half) | 0;
		var hash = ((hash << 5) - hash | 0) + str.charCodeAt((len + half) >> 1) | 0;
		hash = ((hash << 5) - hash | 0) + len | 0;
		return hash;
	}
}

function compute_delta_lines(list1, list2) {
	var hashsize = 1;
	while (hashsize < list1.length) {
		hashsize <<= 1;
	}
	hashsize <<= 1;
	var hashmask = hashsize - 1;
	var ixtab = new Int32Array(hashsize);
	var hashval = new Int32Array(list1.length);
	var link = new Int32Array(list1.length);
	for (var i = list1.length - 1; i >= 0; i--) {
		var h = cheap_hash(list1[i]);
		hashval[i] = h;
		var ix = h & hashmask;
		link[i] = ixtab[ix];
		ixtab[ix] = i;
	}
	result = [];
	var start = 0;
	var end = 0;
	var copy = [];
	for (var i = 0; i < list2.length; i++) {
		var line = list2[i];
		if (copy.length === 0 && end < list1.length && list1[end] === line) {
			end++;
		} else {
			var h = cheap_hash(line);
			var j = ixtab[h & hashmask];
			ix = 0;
			do {
				if (hashval[j] === h && line == list1[j]) {
					ix = j + 1;
					break;
				}
				j = link[j]
			} while (j > 0);
			if (!ix || copy.length !== 0 && line.length === 0) {
				copy.push(line);
			} else {
				if (end || copy.length) {
					result.push([start, end - start, copy]);
					copy = [];
				}
				end = ix;
				start = end - 1;
			}
		}
	}
	if (end || copy.length) {
		result.push([start, end - start, copy]);
	}
	return result;
}

function apply_delta_lines(orig, delta) {
	var result = [];
	for (var i = 0; i < delta.length; i++) {
		var d = delta[i];
		var start = d[0];
		result.push(orig.slice(start, start + d[1]), d[2]);
	}
	return [].concat.apply([], result);
}

function compute_delta(str1, str2) {
	return compute_delta_lines(str1.split('\n'), str2.split('\n'));
}

function apply_delta(orig, delta) {
	return apply_delta_lines(orig.split('\n'), delta).join('\n');
}
