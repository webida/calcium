$(document).ready(function () {
    var code = document.querySelector('#code');
    var types = document.querySelector('#types');
    var props = document.querySelector('#props');
    var varAtPos = document.querySelector('#varAtPos');

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
            if (e.data.varNameAtPos) {
                varAtPos.textContent = 'variable at pos ' +
                    code.selectionStart + ' is ' + e.data.varNameAtPos;
            } else {
                varAtPos.textContent =
                    'no variable at pos ' + code.selectionStart;
            }

            console.log('Message received from worker');
        };
    }
});
