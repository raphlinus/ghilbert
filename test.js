// This test script solves the entire goal-chain test00.
var speed = 10;
function setfirst() {
    GHT.theFirstStep = GHT.getVersion();
}

var steps = [
/*
"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Simplify']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['Simplify']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['Simplify']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['Simplify']();",
"GHT.SaveAs('anything'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Simplify']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['Simplify']();",
"GHT.SaveAs('different');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Distribute']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['Simplify']();",
"GHT.SaveAs('imim2');",

"GHT.theOnclicks['[]']();GHT.theMenu.options['Distribute']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['Simplify']();",
"GHT.SaveAs('imim1');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Simplify']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['imim1']();",
"GHT.SaveAs('himp1');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Distribute']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['Simplify']();",
"GHT.SaveAs('con12');",


"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Simplify']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['Distribute']();",
"GHT.SaveAs('iddlem1');",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['Simplify']();",
"GHT.SaveAs('idd');",

"GHT.theOnclicks['[]']();GHT.theMenu.options['idd']();",
"GHT.SaveAs('id');",



"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Distribute']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['idd']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['Simplify']();",
"GHT.SaveAs('mpd');",

"GHT.theOnclicks['[]']();GHT.theMenu.options['mpd']();",
"GHT.SaveAs('mp');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['id']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['mp']();",
"GHT.SaveAs('idie');",


"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['mp']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['Distribute']();",
"GHT.SaveAs('contract');",

// Level 2
"GHT.setVersion(0);",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Simplify']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['Transpose']();",
"GHT.SaveAs('fie');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['fie']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['Transpose']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('nn1');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['fie']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['Transpose']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['idie']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['Transpose']();",
"GHT.SaveAs('nn2');",


"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Transpose']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['nn2']();",
"GHT.theOnclicks['[1,1]']();GHT.theMenu.options['nn1']();",
"GHT.SaveAs('con3');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Simplify']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['con3']();",
"GHT.SaveAs('nimp2'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['fie']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['con3']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['nn1']();",
"GHT.SaveAs('nimp1');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['mp']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['con3']();",
"GHT.SaveAs('conjnimp'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['fie']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['Distribute']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['Transpose']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('contradict');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['id']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['conjnimp']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['nn2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['idie']();",

"GHT.SaveAs('dfand'); ",
// Level 3
"GHT.setVersion(0);",
                                                         
"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Conjoin']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['nimp1']();",
"GHT.SaveAs('and1');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Conjoin']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['nimp2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['nn1']();",
"GHT.SaveAs('and2');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['imim1']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['con3']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['and1']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['and2']();",
"GHT.SaveAs('anim1');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['con3']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['and2']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['and1']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['con3']();",
"GHT.SaveAs('anim2');",

                                                        

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['and1']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['nimp1']();",
"GHT.SaveAs('andl');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['and1']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['nimp2']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['nn1']();",
"GHT.SaveAs('andr');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['conjnimp']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['and2']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['nn2']();",
"GHT.SaveAs('conj');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['contract']();",
"GHT.SaveAs('anid');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['and1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['Transpose']();",
"GHT.theOnclicks['[2,1,1]']();GHT.theMenu.options['nn1']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['and2']();",
"GHT.SaveAs('ancom'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['anim2']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['anid']();",
"GHT.SaveAs('ancr'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['andr']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['imim1']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['contract']();",
"GHT.theOnclicks['[1,1]']();GHT.theMenu.options['andl']();",
"GHT.SaveAs('import'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['mp']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['import']();",
"GHT.SaveAs('anmp');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['andl']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['ancr']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['andr']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['anmp']();",
"GHT.SaveAs('anim3');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['anim3']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['anim3']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['import']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['ancom']();",
"GHT.SaveAs('prth');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['id']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('dfbi'); ",

// Level 4
"GHT.setVersion(0);",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Equivalate']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['andl']();",
"GHT.SaveAs('def-bi-1'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Equivalate']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['andr']();",
"GHT.SaveAs('def-bi-2');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['andl']();",
"GHT.SaveAs('bi1'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['andr']();",
"GHT.SaveAs('bi2'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['imim1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['imim1']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['def-bi-2']();",

"GHT.SaveAs('imbi1');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.SaveAs('imbi2');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['imim1']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['prth']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['ancr']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1,1]']();GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2,1,2]']();GHT.theMenu.options['imim1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['prth']();",
"GHT.theOnclicks['[2,1,1]']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[2,1,2]']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[2,1,1]']();GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1,2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.SaveAs('bibi1');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['imim1']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['prth']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['ancr']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1,1]']();GHT.theMenu.options['imim1']();",
"GHT.theOnclicks['[2,1,2]']();GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['prth']();",
"GHT.theOnclicks['[2,1,1]']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[2,1,2]']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[2,1,1]']();GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1,2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.SaveAs('bibi2');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['mp']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['bi1']();",
"GHT.SaveAs('mpbi');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['mp']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['bi2']();",
"GHT.SaveAs('mpbir');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['anim1']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['anim1']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.SaveAs('anbi1'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['anim2']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['anim2']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.SaveAs('anbi2');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['con3']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['con3']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['def-bi-2']();",
"GHT.SaveAs('notbi')",

// Level 5
"GHT.setVersion(0);",

"GHT.redecorate()",
"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['bi1']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ancr']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['bi2']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,2,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['bi1']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['ancr']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['bi2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('bicom');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['dfbi']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.SaveAs('biid');",


"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['nn1']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['nn2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['idie']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['bicom~']();",
"GHT.SaveAs('nnbi');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['Transpose']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['con3']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('con3bi');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['and1']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['and2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('dfanbi');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['ancom']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('ancombi');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['anid']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['andr']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('anidbi');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['con12']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['con12']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('con12bi');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['dfanbi']();",
"GHT.theOnclicks['[2,1,2,1]']();GHT.theMenu.options['dfanbi']();",
"GHT.theOnclicks['[2,1,2]']();GHT.theMenu.options['nnbi~']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['con12bi']();",
"GHT.theOnclicks['[2,1,2]']();GHT.theMenu.options['nnbi']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['dfanbi']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['dfanbi']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['ancombi']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['ancombi']();",
"GHT.SaveAs('anass');",


"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['import']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,1]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[1,1,1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('impexp');",


"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['def-bi-1']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['conj']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[1,2]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['def-bi-2']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['idie']();",
"GHT.SaveAs('dfbi3');",
// Level 6
"GHT.setVersion(0);",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['biid']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['term substitute']();GHT.theMenu.options['→']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['term substitute']();GHT.theMenu.options['¬']();",
"GHT.DefThm('or');",
// GHT.Operators['or'] = new Operator('or','or','wff',['wff','wff'],[Infinity,Infinity]);

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['bi2']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['Simplify']();",
"GHT.SaveAs('or2');",
 // GHT.Thms['or2'] = T(O("->"),TV("wff", -53792),T(O("or"),TV("wff", -53793),TV("wff", -53792)));

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[]']();GHT.theMenu.options['arrowees']();GHT.theMenu.options['bi2']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['con3bi']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['Simplify']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['nnbi~']();",
"GHT.SaveAs('or1'); ",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['con3bi~']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['con3bi']();",
"GHT.theOnclicks['[2,2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['nnbi~']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[1,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['nnbi~']();",
"GHT.SaveAs('orim1');",
*/
"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['imbi1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['notbi']();",
"GHT.SaveAs('orbi1');",

"GHT.showTerminals([], null,setfirst)({pageX:0,pageY:0});GHT.theMenu.options['imim2']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['equivalents']();GHT.theMenu.options['df-or']();",
"GHT.SaveAs('orim2'); ",

"GHT.showTerminals([], null, setfirst)({pageX:0,pageY:0});GHT.theMenu.options['imbi1']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['con3bi~']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['con3bi~']();",
"GHT.theOnclicks['[2,1]']();GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['arrowers']();GHT.theMenu.options['notbi']();",
"GHT.SaveAs('orbi2'); ",

"GHT.showTerminals([], null, setfirst)({pageX:0,pageY:0});GHT.theMenu.options['con3bi']();",
"GHT.theOnclicks['[2]']();GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[1]']();GHT.theMenu.options['df-or']();",
"GHT.theOnclicks['[2,2]']();GHT.theMenu.options['nnbi~']();",
//"GHT.SaveAs('orcom'); ",
    /* */
];
GHT.delayTime = speed;
function callback() {

    if (steps.length > 0) {
        var step = steps.shift();
        try {
            eval(step);
            GHT.delayTime = speed;
        } catch (x) {
            console.log(x + " / " + GHT.delayTime);
            steps.unshift(step);
            GHT.delayTime *= 2;
        }
        window.setTimeout(callback, GHT.delayTime);
    }
}
callback();
