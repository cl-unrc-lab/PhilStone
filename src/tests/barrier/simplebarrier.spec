spec simpleBarrier

a1,a2,b1,b2:boolean;

process proc1{
    ea1, eb1 : boolean;
    init: !this.ea1 && !this.eb1 && global.a1 && global.a2 && !global.b1 && !global.b2 && own(global.a1) && own(global.b1) && !own(global.a2) && !own(global.b2) && !av(global.a2) && !av(global.b2);
    
    action staya1(){
    frame: ea1;
    pre: !this.ea1 && global.a1;
    post: !this.ea1;
    }
    
    action enda1(){
    frame: ea1; 
    pre: global.a1 && !this.ea1 && own(global.a1) && own(global.b1);
    post: this.ea1;
    }
    
    action startb1(){
    frame: a1,b1, ea1;
    pre: global.a1 && this.ea1 && !global.b1 && own(global.a1) && own(global.b1);
    post: !global.a1 && global.b1 && !this.ea1 && own(global.a1) && own(global.b1);
    }

    action stayb1(){
    frame: eb1;
    pre: !this.eb1 && global.b1;
    post: !this.eb1;
    }
    
    action endb1(){
    frame: eb1;
    pre: global.b1 && !this.eb1 && own(global.a1) && own(global.b1);
    post: this.eb1 && own(global.a1) && own(global.b1);
    }
    
    action starta1(){
    frame: a1,b1, eb1;
    pre: global.b1 && this.eb1 &&  own(global.a1) && own(global.b1);
    post: !global.b1 && global.a1 && !this.eb1 && own(global.a1) && own(global.b1);
    }
    
    invariant: AG[!this.ea1 || EX[global.b1]] && AG[!this.eb1 || EX[global.a1]] && AG[!(this.ea1 && this.eb1)] && EF[this.ea1];
}

process proc2{
    ea2, eb2 : boolean;
    init: !this.ea2 && !this.eb2 && global.a2 && global.a1 && !global.b2 && !global.b1 && own(global.a2) && own(global.b2) && !own(global.a1) && !own(global.b1) &&  !av(global.a1) && !av(global.b1);
    
    action staya2(){
    frame: ea2;
    pre: !this.ea2 && global.a2;
    post: !this.ea2;
    }
    
    action enda2(){
    frame: ea2; 
    pre: global.a2 && !this.ea2 && own(global.a2) && own(global.b2);
    post: this.ea2;
    }
    
    action startb2(){
    frame: a2,b2, ea2;
    pre: global.a2 && this.ea2 && !global.b2 && own(global.a2) && own(global.b2);
    post: !global.a2 && global.b2 && !this.ea2 && own(global.a2) && own(global.b2);
    }

    action stayb2(){
    frame: eb2;
    pre: !this.eb2 && global.b2;
    post: !this.eb2;
    }
    
    action endb2(){
    frame: eb2;
    pre: global.b2 && !this.eb2 && own(global.a2) && own(global.b2);
    post: this.eb2 && own(global.a2) && own(global.b2);
    }
    
    action starta1(){
    frame: a2,b2, eb2;
    pre: global.b2 && this.eb2 &&  own(global.a2) && own(global.b2);
    post: !global.b2 && global.a2 && !this.eb2 && own(global.a2) && own(global.b2);
    }
    
    invariant: AG[!this.ea2 || EX[global.b2]] && AG[!this.eb2 || EX[global.a2]] && AG[!(this.ea2 && this.eb2)] && EF[this.ea2];
}


main(){
        p1:proc1;
        p2:proc2;
        run p1();
        run p2();
}
property: AG[!(p1.ea1 && p2.eb2)];