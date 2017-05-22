bool stop = false;

inline voter(first, second, third){
    int counter = 1, possible_value = -1;
    bool verified = false;
    printf("Case of %d %d %d\n", first, second, third)
    T0: if
        :: stop == true -> goto S6;
        :: else -> goto S0
        fi

    S0: if
        :: first == second -> counter++; possible_value = first; verified = true;
        :: else -> skip;
        fi
        goto S1;

    S1: if
        :: verified == true -> goto S7;
        :: else -> goto S2;
        fi

    S2: if
        :: first == third -> counter++; possible_value = first; verified = true;
        :: else -> skip;
        fi
        goto S3
    
    S3: if
        :: verified == true -> goto S7;
        :: else -> goto S4;
        fi
    
    S4: if
        :: second == third -> counter++; possible_value = second; verified = true;
        :: else -> skip;
        fi
        goto S5;

    S5: if
        :: verified == true -> goto S7;
        :: else -> goto S6;
        fi
    S6: printf("It was not possible to calculate the insulin dose; please try again\n");
        goto S8;

    S7: printf("%d\n",possible_value);
        goto S8;

    S8: 
}


proctype Timer(){
    int timer = 1,i;
    for(i:1..4){
        timer++
    }
    stop = true;
    printf("Timeout\n");
}


proctype Voter(){
        int first, second, third;
        select(first : 1..3);
        select(second : 1..3);
        select(third : 1..3);
        voter(first,second,third);
}

init{
    run Timer();
    run Voter();
}