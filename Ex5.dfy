class {:autocontracts} Quack<Data(0)>
{ // (0) necessary to say the type can be initialised by Dafny
    var buf: array<Data>;
    var m: int, n: int;

    ghost var shadow: seq<Data>;

    predicate Valid()
    { buf.Length!=0 && 0<=m<=n<=buf.Length && shadow==buf[m..n] }

    constructor(size: int)
    requires size>0;
    ensures shadow == [];
    ensures fresh(buf);
    {   buf := new Data[size];
        m, n:= 0, 0;
        shadow:= [];
    }

    method Empty() returns (e: bool)
    ensures e <==> shadow==[]
    { e := m==n; }
  
    method Qop() returns(d: Data) // + Push() works as a queue
    requires shadow != [];
    ensures       d == old(shadow)[0] // get head
    ensures  shadow == old(shadow)[1..]
    {   d, m:= buf[m], m+1;
        shadow:= shadow[1..];
    }
    method Pop() returns(x: Data) // + Push() works as a stack
    requires shadow != [] 
    ensures       x == old(shadow)[|old(shadow)|-1] // get tail
    ensures  shadow == old(shadow)[..|old(shadow)|-1]
    {   x, n:= buf[n-1], n-1;
        shadow:= shadow[..|shadow|-1];
    }
    method Push(x: Data)  // + Pop():a stack,  + Qop():a queue
    ensures shadow == old(shadow) + [x]; // new tail
    {   if n==buf.Length
        {   var b:= buf; // have b of old size
            if m==0
                { b:= new Data[2*buf.Length]; } // b double size
            forall (i | 0<=i<n-m)
                { b[i]:= buf[m+i]; }
            buf, m, n:= b, 0, n-m;
        }
        buf[n], n:= x, n+1;
        shadow:= shadow + [x];
    }

    method HeadTail()
        // not change cases 
        ensures n-m <  2 ==> (buf == old(buf))
        ensures n == old(n) && m == old(m)
        // swap the both elements 
        ensures n-m >= 2 ==> buf[n-1] == old(buf[m]) 
        ensures n-m >= 2 ==> buf[m] == old(buf[n-1]) 
        ensures n-m >= 2 ==> 
            // things not changed 
            forall x :: m < x < n -1 ==> buf[x] == old(buf[x]) 
    {
        // do nothing if there nothing or only one els  
        if (n-m >= 2 ){
            buf[n-1], buf[m]:= buf[m], buf[n-1];
            shadow:= [shadow[|shadow|-1]] + shadow[1..|shadow|-1] + [shadow[0]];
        }
    }
} // end of Quack class

method Main()
{   var q:= new Quack<char>(10);
    var l: char;
    q.Push('r'); q.Push('s'); q.Push('k'); q.Push('o'); q.Push('w');
    l:= q.Pop(); print l;  
    q.HeadTail();
    l:= q.Qop(); print l;
    l:= q.Pop(); print l;
    q.HeadTail();
    l:= q.Qop(); print l;    
    l:= q.Qop(); print l;        
    var e: bool:= q.Empty();
    if e {print "\nqueue empty\n";} else {print "\nqueue not empty\n";}
}
