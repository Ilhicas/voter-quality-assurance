inline voter(first, second, third){
    int counter = 1, possible_value = -1;
    bool verified = false;
    printf("Case of %d %d %d\n", first, second, third)
    if
    :: first == second -> counter++; possible_value = first; verified = true;
    :: else -> skip
    fi

    if
    :: first == third && verified == false -> counter++; possible_value = first; verified = true;
    :: else -> skip
    fi
    
    if
    :: second == third && verified == false -> counter++; possible_value = second; verified = true;
    :: else -> skip
    fi

    if
    :: counter == 1 -> printf("It was not possible to calculate the insulin dose; please try again\n")
    :: else -> printf("%d\n",possible_value)
    fi
}

proctype Voter1(){
    atomic{
        voter(1,2,3);
    }
}

proctype Voter2(){
    atomic{
        voter(1,1,1);
    }
}

proctype Voter3(){
    atomic{
        voter(1,2,2);
    }
}

init{
    run Voter1();
    run Voter2();
    run Voter3();
}