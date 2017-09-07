// Copyright 2017 Raph Levien. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

'use strict';

// json info is available globally
var json = null;

function replaceRight(newNodes) {
    let right = document.getElementById("right");
    let child;
    while (child = right.firstChild) {
        right.removeChild(child);
    }
    let xd = document.createElement("div");
    let x = document.createTextNode("x");
    xd.className = "close";
    xd.setAttribute("title", "Close");
    xd.addEventListener("click", function() {
        right.className = "hidden";
    });
    xd.appendChild(x);
    right.appendChild(xd);
    right.className = "visible";

    for (let child of newNodes) {
        right.appendChild(child);
    }
}

function createRightPane(info) {
    let result = [];
    let title = document.createElement("h1");
    let a = document.createElement("a");
    let link = info.link;
    a.appendChild(document.createTextNode(link));
    a.setAttribute("href", link + ".html");
    title.appendChild(a);
    result.push(title);
    let comment = document.createElement("div");
    comment.className = "text";
    comment.appendChild(document.createTextNode(info.comment));
    result.push(comment);
    let ts = document.createElement("div");
    ts.className = "text";
    ts.appendChild(document.createTextNode("\\( " + info.typeset + " \\)"));
    result.push(ts);
    MathJax.Hub.Queue(["Typeset",MathJax.Hub,ts]);
    return result;
}

function getEl(step_ix) {
    return document.getElementById("s" + step_ix);
}

function addDefListeners(step, def) {
    let ref = getEl(def);
    step.addEventListener("mouseover", function() {
        step.className = "cur_step";
        ref.className = "ref_step";
    });
    step.addEventListener("mouseout", function() {
        step.className = "";
        ref.className = "";
    });
}

function chaseRef(step_ix) {
    let ref_step = json["s" + step_ix];
    if (ref_step && "def" in ref_step) {
        return ref_step.def;
    } else {
        return step_ix;
    }
}

function addRefListeners(step, refs) {
    step.addEventListener("mouseover", function() {
        step.className = "cur_step";
        for (let ref_ix of refs) {
            let ref = getEl(chaseRef(ref_ix));
            ref.className = "ref_step";
        }
    });
    step.addEventListener("mouseout", function() {
        step.className = "";
        for (let ref_ix of refs) {
            let ref = getEl(chaseRef(ref_ix));
            ref.className = "";
        }
    });
}

function applyJson(json) {
    var steps = document.querySelectorAll(".s span");
    for (let step of steps) {
        let info = json[step.id];
        if (!info) { continue; }
        if ("hover" in info) {
            step.setAttribute("title", info.hover);
            step.classList.add("clickable");
            step.addEventListener("click", function() {
                replaceRight(createRightPane(info));
            });
            addRefListeners(step, info.refs);
        } else if ("def" in info) {
            addDefListeners(step, info.def);
        }
    }
}

function loadInfo() {
    let xhr = new XMLHttpRequest();
    xhr.responseType = 'json';
    let thmname = document.querySelector(".thmname").firstChild.nextSibling.data.trim();
    xhr.open('get', thmname + '.json', true);
    xhr.onreadystatechange = function() {
        if (xhr.readyState == 4 && xhr.status == 200) {
            // console.log(xhr.response);
            json = xhr.response;
            applyJson(json);
        }
    };
    xhr.send();
}

loadInfo();
