function changeOptions(selectEl) {
    let selectedValue = selectEl.options[selectEl.selectedIndex].value;
    let subForms = document.getElementsByClassName('form-group')
    for (let i = 0; i < subForms.length; i += 1) {
        if (selectedValue === subForms[i].name) {
            subForms[i].setAttribute('style', 'display:block')
        } else {
            subForms[i].setAttribute('style', 'display:none')
        }
    }
}

function showDetails() {
    var x = document.getElementById('showDetailsDiv');
    if (x.style.display === 'none') {
        x.style.display = 'block';
    } else {
        x.style.display = 'none';
    }
}

(function() {
    $('#form_1 > input').keyup(function() {

        var empty = false;
        $('#form_1 > input').each(function() {
            if ($(this).val() == '') {
                empty = true;
            }
        });

        if (empty) {
            $('#submit1').attr('disabled', 'disabled');
        } else {
            $('#submit1').removeAttr('disabled');
        }
    });

    $('#form_2 > input').keyup(function() {
        var empty = false;
        $('#form_2 > input').each(function() {
            if ($(this).val() == '') {
                empty = true;
            }
        });

        if (empty) {
            $('#submit2').attr('disabled', 'disabled');
        } else {
            $('#submit2').removeAttr('disabled');
        }
    });

    $('#form_3').keyup(function() {
        var empty = false;

        $('#mealtime > input').each(function() {
            if ($(this).val() == '') {
                empty = true;
            }
        });

        var count_input1_not_empty= 0;
        var count_input2_not_empty= 0;

        $('#k_activity > input').each(function() {
            if ($(this).val() != '') {
                count_input1_not_empty++;
            }
        });

        $('#k_drops > input').each(function() {
            if ($(this).val() != '') {
                count_input2_not_empty++;
            }
        });

        if (count_input1_not_empty < 2 || count_input2_not_empty < 2) {
            empty = true;
        }

        if (count_input1_not_empty != count_input2_not_empty) {
            empty = true;
        }

        if ($('#a1').val() != '') {
            if ($('#k1').val() == '')
                empty = true;
        }
        if ($('#a2').val() != '') {
            if ($('#k2').val() == '')
                empty = true;
        }
        if ($('#a3').val() != '') {
            if ($('#k3').val() == '')
                empty = true;
        }
        if ($('#a4').val() != '') {
            if ($('#k4').val() == '')
                empty = true;
        }
        if ($('#a5').val() != '') {
            if ($('#k5').val() == '')
                empty = true;
        }
        if ($('#a6').val() != '') {
            if ($('#k6').val() == '')
                empty = true;
        }
        if ($('#a7').val() != '') {
            if ($('#k7').val() == '')
                empty = true;
        }
        if ($('#a8').val() != '') {
            if ($('#k8').val() == '')
                empty = true;
        }
        if ($('#a9').val() != '') {
            if ($('#k9').val() == '')
                empty = true;
        }

        if ($('#a10').val() != '') {
            if ($('#k10').val() == '')
                empty = true;
        }


        if ($('#k1').val() != '') {
            if ($('#a1').val() == '')
                empty = true;
        }
        if ($('#k2').val() != '') {
            if ($('#a2').val() == '')
                empty = true;
        }
        if ($('#k3').val() != '') {
            if ($('#a3').val() == '')
                empty = true;
        }
        if ($('#k4').val() != '') {
            if ($('#a4').val() == '')
                empty = true;
        }
        if ($('#k5').val() != '') {
            if ($('#a5').val() == '')
                empty = true;
        }
        if ($('#k6').val() != '') {
            if ($('#a6').val() == '')
                empty = true;
        }
        if ($('#k7').val() != '') {
            if ($('#a7').val() == '')
                empty = true;
        }
        if ($('#k8').val() != '') {
            if ($('#a8').val() == '')
                empty = true;
        }
        if ($('#k9').val() != '') {
            if ($('#a9').val() == '')
                empty = true;
        }

        if ($('#k10').val() != '') {
            if ($('#a10').val() == '')
                empty = true;
        }

        if (empty) {
            $('#submit3').attr('disabled', 'disabled');
        } else {
            $('#submit3').removeAttr('disabled');
        }
    });


})()
