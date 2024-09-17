
/*
* This is a version of the arbiter problem
*/

spec arbiter8
send1,send2,send3,send4,send5,send6,send7,send8, r1,r2,r3,r4,r5,r6,r7,r8: prim_boolean;
process process1{
    g1, hasToken: boolean;
    init: !this.g1 && !global.r1; 
    
    action giveGrant(){
        frame: g1;
        pre : global.r1;
        post: this.g1;
    }
    
    action downGrant(){
        frame: g1;
        pre : global.r1 || !global.r1 ;
        post: !this.g1;
    }
    invariant: AG[EF[global.send2]]&&AG[EF[this.g1]] && AG[EF[!this.g1]];
    }process process2{
    g2, hasToken: boolean;
    init: !this.g2 && !global.r2; 
    
    action giveGrant(){
        frame: g2;
        pre : global.r2;
        post: this.g2;
    }
    
    action downGrant(){
        frame: g2;
        pre : global.r2 || !global.r2 ;
        post: !this.g2;
    }
    invariant: AG[EF[global.send3]]&&AG[EF[this.g2]] && AG[EF[!this.g2]];
    }process process3{
    g3, hasToken: boolean;
    init: !this.g3 && !global.r3; 
    
    action giveGrant(){
        frame: g3;
        pre : global.r3;
        post: this.g3;
    }
    
    action downGrant(){
        frame: g3;
        pre : global.r3 || !global.r3 ;
        post: !this.g3;
    }
    invariant: AG[EF[global.send4]]&&AG[EF[this.g3]] && AG[EF[!this.g3]];
    }process process4{
    g4, hasToken: boolean;
    init: !this.g4 && !global.r4; 
    
    action giveGrant(){
        frame: g4;
        pre : global.r4;
        post: this.g4;
    }
    
    action downGrant(){
        frame: g4;
        pre : global.r4 || !global.r4 ;
        post: !this.g4;
    }
    invariant: AG[EF[global.send5]]&&AG[EF[this.g4]] && AG[EF[!this.g4]];
    }process process5{
    g5, hasToken: boolean;
    init: !this.g5 && !global.r5; 
    
    action giveGrant(){
        frame: g5;
        pre : global.r5;
        post: this.g5;
    }
    
    action downGrant(){
        frame: g5;
        pre : global.r5 || !global.r5 ;
        post: !this.g5;
    }
    invariant: AG[EF[global.send6]]&&AG[EF[this.g5]] && AG[EF[!this.g5]];
    }process process6{
    g6, hasToken: boolean;
    init: !this.g6 && !global.r6; 
    
    action giveGrant(){
        frame: g6;
        pre : global.r6;
        post: this.g6;
    }
    
    action downGrant(){
        frame: g6;
        pre : global.r6 || !global.r6 ;
        post: !this.g6;
    }
    invariant: AG[EF[global.send7]]&&AG[EF[this.g6]] && AG[EF[!this.g6]];
    }process process7{
    g7, hasToken: boolean;
    init: !this.g7 && !global.r7; 
    
    action giveGrant(){
        frame: g7;
        pre : global.r7;
        post: this.g7;
    }
    
    action downGrant(){
        frame: g7;
        pre : global.r7 || !global.r7 ;
        post: !this.g7;
    }
    invariant: AG[EF[global.send8]]&&AG[EF[this.g7]] && AG[EF[!this.g7]];
    }process process8{
    g8, hasToken: boolean;
    init: !this.g8 && !global.r8; 
    
    action giveGrant(){
        frame: g8;
        pre : global.r8;
        post: this.g8;
    }
    
    action downGrant(){
        frame: g8;
        pre : global.r8 || !global.r8 ;
        post: !this.g8;
    }
    invariant: AG[EF[global.send1]]&&AG[EF[this.g8]] && AG[EF[!this.g8]];
    }
main(){
p1:process1;
    p2:process2;
    p3:process3;
    p4:process4;
    p5:process5;
    p6:process6;
    p7:process7;
    p8:process8;
    run p1();
    run p2();
    run p3();
    run p4();
    run p5();
    run p6();
    run p7();
    run p8();
    
}
property: G[!global.r1 || F[p1.g1]]&&G[!global.r2 || F[p2.g2]]&&G[!global.r3 || F[p3.g3]]&&G[!global.r4 || F[p4.g4]]&&G[!global.r5 || F[p5.g5]]&&G[!global.r6 || F[p6.g6]]&&G[!global.r7 || F[p7.g7]]&&G[!global.r8 || F[p8.g8]]&&G[!(p1.g1 && p1.g1)]&&G[!(p1.g1 && p2.g2)]&&G[!(p1.g1 && p3.g3)]&&G[!(p1.g1 && p4.g4)]&&G[!(p1.g1 && p5.g5)]&&G[!(p1.g1 && p6.g6)]&&G[!(p1.g1 && p7.g7)]&&G[!(p1.g1 && p8.g8)]&&G[!(p2.g2 && p2.g2)]&&G[!(p2.g2 && p3.g3)]&&G[!(p2.g2 && p4.g4)]&&G[!(p2.g2 && p5.g5)]&&G[!(p2.g2 && p6.g6)]&&G[!(p2.g2 && p7.g7)]&&G[!(p2.g2 && p8.g8)]&&G[!(p3.g3 && p3.g3)]&&G[!(p3.g3 && p4.g4)]&&G[!(p3.g3 && p5.g5)]&&G[!(p3.g3 && p6.g6)]&&G[!(p3.g3 && p7.g7)]&&G[!(p3.g3 && p8.g8)]&&G[!(p4.g4 && p4.g4)]&&G[!(p4.g4 && p5.g5)]&&G[!(p4.g4 && p6.g6)]&&G[!(p4.g4 && p7.g7)]&&G[!(p4.g4 && p8.g8)]&&G[!(p5.g5 && p5.g5)]&&G[!(p5.g5 && p6.g6)]&&G[!(p5.g5 && p7.g7)]&&G[!(p5.g5 && p8.g8)]&&G[!(p6.g6 && p6.g6)]&&G[!(p6.g6 && p7.g7)]&&G[!(p6.g6 && p8.g8)]&&G[!(p7.g7 && p7.g7)]&&G[!(p7.g7 && p8.g8)];
        assumption: G[F[p1.hasToken]] &&G[F[p2.hasToken]] &&G[F[p3.hasToken]] &&G[F[p4.hasToken]] &&G[F[p5.hasToken]] &&G[F[p6.hasToken]] &&G[F[p7.hasToken]] &&G[F[p8.hasToken]] ;