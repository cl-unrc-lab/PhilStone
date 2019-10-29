spec barrier

sa1, ea1, sb1, eb1,sa2,ea2, sb2, eb2: boolean;

process proc(mysa:boolean,myea:boolean,mysb:boolean, myeb:boolean, othersa:boolean,otherea:boolean,othersb:boolean, othereb:boolean){
    init: mysa && !myea && !mysb && !myeb && own(mysa) && own(myea) && own(mysb) && own(myeb);
    
    action finishA(){
        frame: mysa, myea;
        pre: mysa && own(mysa) && own(myea);
        post: !mysa && myea && own(mysa) && own(myea);
    }
    
    action startB(){
        frame: myea, mysb;
        pre: myea && own(mysb) && own(myea);
        post: !myea && mysb && own(mysb) && own(myea);
    }

    action finishB(){
        frame: mysb, myeb;
        pre: mysb && own(myeb) && own(mysb);
        post: !mysb && myeb && own(mysb) && own(myeb);
    }
    
     action startA(){
        frame: myeb, mysa;
        pre: myeb && own(mysa) && own(myeb);
        post: !myeb && mysa && own(mysa) && own(myeb);
    }
    invariant: AG[!(mysa && myea)]&& AG[!(mysa&&mysb)] && AG[!(mysa&&myeb)] && AG[!(myea&&mysb)] && AG[!(myea && myeb)] && AG[!(mysb && myeb)] && AG[!myea || AX[mysb]] && AG[!mysb || AX[myeb]] && AG[!myeb || AX[mysa]] && EF[myeb];
}
main(){
        p1:proc;
        p2:proc;
        run p1(sa1,ea1,sb1,eb1,sa2,ea2,sb2,eb2);
        run p2(sa2,ea2,sb2,eb2,sa1,ea1,sb1,eb1);
}
property: AG[!(global.sa1 && global.sb2) && !(global.sa2 && global.sb1)] && EF[global.eb1] && EF[global.eb2];




