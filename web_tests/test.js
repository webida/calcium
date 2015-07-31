$(document).ready(function () {
    var code = document.querySelector('#code');
    var types = document.querySelector('#types');
    var props = document.querySelector('#props');
    var varAtPos = document.querySelector('#varAtPos');
    var varOccurrences = document.querySelector('#varOccurrences');
    var onFunctionOrReturnKeyword = document.querySelector('#onFunctionOrReturnKeyword');
    var returnList = document.querySelector('#returnList');
    var onThisKeyword = document.querySelector('#onThisKeyword');
    var thisList = document.querySelector('#thisList');

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
            onFunctionOrReturnKeyword.textContent = 'on function or return keyword? ' +
                !!e.data.onFunctionOrReturnKeyword;
            onThisKeyword.textContent = 'on this keyword? ' +
                !!e.data.onThisKeyword;

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
            if (e.data.onFunctionOrReturnKeyword) {
                returnList.textContent = '';
                e.data.returnList.forEach(function (e) {
                    "use strict";
                    returnList.textContent += e.start + ' ~ ' + e.end + ', ';
                });
            } else {
                returnList.textContent = 'N/A';
            }

            if (e.data.onThisKeyword) {
                thisList.textContent = '';
                e.data.thisList.forEach(function (e) {
                    "use strict";
                    thisList.textContent += e.start + ' ~ ' + e.end + ', ';
                });
            } else {
                thisList.textContent = 'N/A';
            }

            console.log('Message received from worker');
        };
    }
});
