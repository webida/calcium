$(document).ready(function () {
    var code = document.querySelector('#code');
    var types = document.querySelector('#types');
    var props = document.querySelector('#props');
    var varAtPos = document.querySelector('#varAtPos');
    var varOccurrences = document.querySelector('#varOccurrences');
    var onFunctionKeyword = document.querySelector('#onFunctionKeyword');
    var returnList = document.querySelector('#returnList');

    if (!!window.Worker) {
        var worker = new Worker('worker.js');
        code.onchange = code.onkeyup = function () {
            console.log('Message posted to worker');
            worker.postMessage({code: code.value, pos: code.selectionStart});
        };

        worker.onmessage = function (e) {
            console.log(e);
            types.textContent = 'x\'s type names: ' + e.data.typeNames;
            props.textContent = 'x\'s property names: ' + e.data.propNames;
            onFunctionKeyword.textContent = 'on function keyword? ' +
                !!e.data.onFunctionKeyword;
            if (e.data.varNameAtPos) {
                varAtPos.textContent = 'variable at pos ' +
                    code.selectionStart + ': ' + e.data.varNameAtPos;
                // showing the occurrences
                varOccurrences.textContent = 'Occurrences of the variable: ';
                e.data.varOccurrences.forEach(function (e) {
                    "use strict";
                    // show each occurrences
                    varOccurrences.textContent += e.start + ' ~ ' + e.end + ', ';
                });
            } else {
                varAtPos.textContent =
                    'no variable at pos ' + code.selectionStart;
                varOccurrences.textContent = '';
            }
            if (e.data.onFunctionKeyword) {
                returnList.textContent = '';
                e.data.returnList.forEach(function (e) {
                    "use strict";
                    returnList.textContent += e.start + ' ~ ' + e.end + ', ';
                });
            } else {
                returnList.textContent = 'N/A';
            }

            console.log('Message received from worker');
        };
    }
});
