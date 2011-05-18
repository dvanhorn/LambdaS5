// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/**
* @name: S15.5.4.12_A1_T9;
* @section: 15.5.4.12;
* @assertion: String.prototype.search (regexp);
* @description: Argument is function call, and instance is String object with overrided toString and valueOf functions;
*/


// Converted for Test262 from original Sputnik source

ES5Harness.registerTest( {
id: "S15.5.4.12_A1_T9",

path: "15_Native\15.5_String_Objects\15.5.4_Properties_of_the_String_Prototype_Object\15.5.4.12_String.prototype.search\S15.5.4.12_A1_T9.js",

assertion: "String.prototype.search (regexp)",

description: "Argument is function call, and instance is String object with overrided toString and valueOf functions",

test: function testcase() {
   var __obj = {
    valueOf:function(){},
    toString:void 0
};

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
//since ToString(undefined) evaluates to "undefined" search(undefined) evaluates to search("undefined")
if (new String(__obj).search(function(){}()) !== 0) {
  $ERROR('#1: __obj = {valueOf:function(){}, toString:void 0}; new String(__obj).search(function(){}()) === 0. Actual: '+new String(__obj).search(function(){}()) );
}
//
//////////////////////////////////////////////////////////////////////////////

 }
});
