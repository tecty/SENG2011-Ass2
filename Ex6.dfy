predicate Sorted(a:array<int>, low:int, high:int) 
    reads a 
    // index must not out of bound 
    requires 0<= low <= high  <= a.Length
{
    forall j,k:: 0<=j<k<high ==> a[j]<=a[k] 
}

predicate SortedExcept(a:array<int>, high:int, except:int )
    reads a 
    requires 0<= except <= high  <= a.Length
{
    forall j,k:: (0<=j<k<high && j != except && k != except) ==> a[j]<=a[k] 
}

// predicate unShifted(a:array<int>, a_old:seq<int>, low:int, high:int)
//     reads a 
//     requires a.Length == |a_old|
//     requires 0<= low <= high  < a.Length
// {
//     // unshifted should be all the same 
//     (forall i:: (low <= i < high) ==> a[i] == a_old[i] ) &&
//     // use this for all we can show that the mulitset of these tow things are same 
//     multiset(a[low..high]) == multiset(a_old[low..high])
// }

// predicate Shifted(a:array<int>, a_old:seq<int>, low:int, high:int)
//     reads a 
//     requires a.Length == |a_old|
//     requires 0< low <= high  <= a.Length
// {
//     // define of shuffle 
//     (forall i ::  (low <= i < high )==> a[i] == a_old[i-1]) && 
//     // proof both part are same 
//     a[low .. high] == a_old[low-1..high-1] && 
//     // proof the multiset 
//     multiset(a[low .. high]) == multiset(a_old[low-1..high-1])
// }

lemma arrayEqualToMultiset(a:array<int>, b:array<int>)
    requires a[..] == b[..]
    ensures multiset(a[..]) == multiset(b[..])
{}

lemma arrayInjectEqual(a: array<int>, a_old:array<int>,up:int,injectPoint:int, injectValue:int)
    // the old and new array will have basic property 
    requires a.Length == a_old.Length;
    requires 0 <= injectPoint<= up < a.Length
    // then, below the inject point and they are equal 
    requires a[..injectPoint] == a_old[..injectPoint];
    // then between the inject point till upper bound is shiffted 
    requires a[injectPoint+1 .. up+1] == a_old[injectPoint..up]
    // then element after upper bound ar same 
    requires a[up+1 ..] == a_old[up+1..]
    // also require the inject value will be the value pushed out 
    requires injectValue == a_old[up];

    // critical area will be the same 
    ensures a[injectPoint+1 .. up+1] +[injectValue] == a_old[injectPoint..up +1]
    ensures multiset([injectValue]+ a[injectPoint+1 .. up+1]) == multiset(a_old[injectPoint..up +1])
    // then the final sequence will be identical 
    ensures a[..injectPoint]  + a[injectPoint+1 .. up+1] +[injectValue]+ a[up+1 ..]  == a_old[..]
    // hence they will have a equal multi set 
    ensures 
        multiset(a[..injectPoint])  + multiset(a[injectPoint+1 .. up+1]) 
        + multiset([injectValue])+ multiset(a[up+1 ..])  == multiset(a_old[..])
    ensures a[injectPoint+1 .. up+1]+[injectValue]+a[up+1 ..] == a_old[injectPoint..]
    ensures multiset(a[injectPoint+1 .. up+1]) + multiset([injectValue])+ multiset(a[up+1 ..])  == multiset(a_old[injectPoint..])
    ensures a[injectPoint +1 .. up+1] + a[up+1 ..] == a[injectPoint +1 ..]
    ensures  multiset(a[injectPoint+1 .. up+1]) + multiset(a[up+1 ..]) == multiset(a[injectPoint +1 ..]) 
    // even a simplify version 
    ensures multiset(a[..injectPoint]) + multiset(a[injectPoint +1 ..]) + multiset([injectValue]) == multiset(a_old[..])
{}

lemma Shifted(a: array<int>, a_old:array<int>,up:int,injectPoint:int)
    requires a.Length == a_old.Length;
    requires 0 <= injectPoint<= up < a.Length
    requires forall i :: injectPoint < i <= up  ==> a[i] == a_old[i-1]
    ensures a[injectPoint+1..up+1] == a_old[injectPoint..up ]
{}


method InsertionSortShuffle(a: array<int>)
requires a.Length>1
ensures Sorted(a, 0, a.Length);
ensures multiset(a[..]) == multiset(old(a[..]));
modifies a;
{
    var up:=1;
    var injectValue:= a[up];
    var injectPoint:= up;


    while (up < a.Length  )
        decreases a.Length - up 
        invariant 1 <= up <= a.Length;
        invariant 0<= injectPoint <= up 
        invariant Sorted(a, 0, up);
        invariant multiset(a[..]) == multiset(old(a[..]));
        // invariant forall injectPoint < i <= up 
    {
        injectValue := a[up];
        injectPoint := up;
        while (injectPoint >= 1 && a[injectPoint-1] > a[injectPoint])
            decreases injectPoint
            invariant 0 <= injectPoint <= up;
            invariant forall i,j:: (0<=i<j<=up && j!=injectPoint)==>a[i]<=a[j];
            invariant multiset(a[..injectPoint]) == multiset(old(a)[..injectPoint]);
            invariant multiset( a[injectPoint+1..up+1]) == multiset( old(a)[injectPoint+1.. up+1])
            invariant injectPoint != up ==> injectPoint == old(injectPoint-1)
            invariant injectPoint != up ==> a[injectPoint] == old(a[injectPoint])
        {
            a[injectPoint] := a[injectPoint-1];
            injectPoint:=injectPoint-1;
        }
        Shifted(a, old(a),up, injectPoint);
        // lemma for proving multiset is eqal 
        arrayInjectEqual(a, old(a), up ,injectPoint,injectValue);
        a[injectPoint] :=  injectValue;
        up:=up+1;
    }
}
method Main()
{
// do not change this code
var a := new int[][6,2,0,6,3,5,0,4,1,6,0]; // testcase 1
var msa := multiset(a[..]);
InsertionSortShuffle(a);
assert Sorted(a, 0, a.Length);
var msa_post := multiset(a[..]);
assert msa==msa_post;
var b := new int[][8,7]; // testcase 2
InsertionSortShuffle(b);
print a[..], b[..];
}
