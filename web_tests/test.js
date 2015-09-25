$(document).ready(function () {
    var code = document.querySelector('#code');
    var types = document.querySelector('#types');
    var props = document.querySelector('#props');
    var varAtPos = document.querySelector('#varAtPos');
    var varOccurrences = document.querySelector('#varOccurrences');
    var onEscapingStatement = document.querySelector('#onEscapingStatement');
    var escapingList = document.querySelector('#escapingList');
    var onThisKeyword = document.querySelector('#onThisKeyword');
    var thisList = document.querySelector('#thisList');
    var surroundingNode = document.querySelector('#surroundingNode');

    if (!!window.Worker) {
        var worker = new Worker('worker.js');
        code.onchange = code.onkeyup = function () {
            console.log('Message posted to worker');
            worker.postMessage({
                code: code.value,
                start: code.selectionStart,
                end: code.selectionEnd});
        };

        worker.onmessage = function (e) {
            console.log(e);
            types.textContent = 'x\'s type names: ' + e.data.typeNames;
            props.textContent = 'x\'s property names: ' + e.data.propNames;
            onEscapingStatement.textContent = 'on function or escaping keyword? ' +
                !!e.data.onEscapingStatement;
            onThisKeyword.textContent = 'on this keyword? ' +
                !!e.data.onThisKeyword;

            if (e.data.varNameAtPos) {
                varAtPos.textContent = 'variable at pos ' +
                    code.selectionStart + ': ' + e.data.varNameAtPos;
                // showing the occurrences
                varOccurrences.textContent = 'Occurrences of the variable: ';
                e.data.varOccurrences.forEach(function (e) {
                    'use strict';
                    // show each occurrences
                    varOccurrences.textContent += e.start + ' ~ ' + e.end + ', ';
                });
            } else {
                varAtPos.textContent =
                    'no variable at pos ' + code.selectionStart;
                varOccurrences.textContent = '';
            }
            if (e.data.onEscapingStatement) {
                escapingList.textContent = '';
                e.data.escapingList.forEach(function (e) {
                    'use strict';
                    escapingList.textContent += e.start + ' ~ ' + e.end + ', ';
                });
            } else {
                escapingList.textContent = 'N/A';
            }

            if (e.data.onThisKeyword) {
                thisList.textContent = '';
                e.data.thisList.forEach(function (e) {
                    'use strict';
                    thisList.textContent += e.start + ' ~ ' + e.end + ', ';
                });
            } else {
                thisList.textContent = 'N/A';
            }

            surroundingNode.textContent =
                'Selection: ' + code.selectionStart + '~' +
                code.selectionEnd + ' => Surrounding node: ';
            surroundingNode.textContent +=
                e.data.typeData.nodeStart + '~' +
                e.data.typeData.nodeEnd + '\n' +
                'types are ' + e.data.typeData.typeString;

            console.log('Message received from worker');
        };
    }
});
