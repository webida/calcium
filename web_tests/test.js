$(document).ready(function () {
    var code = document.querySelector('#code');
    var types = document.querySelector('#types');
    var props = document.querySelector('#props');

    if (!!window.Worker) {
        var worker = new Worker('worker.js');
        code.onchange = code.onkeyup = function () {
            console.log('Message posted to worker');
            worker.postMessage({code: code.value});
        };

        worker.onmessage = function (e) {
            console.log(e);
            types.textContent = 'x\'s type names: ' + e.data.typeNames;
            props.textContent = 'x\'s property names: ' + e.data.propNames;
            console.log('Message received from worker');
        };
    }
});
