predicate Sorted(a:array<int>, low:int, high:int) 
    reads a 
    // index must not out of bound 
    requires 0 <=low
    requires     high <= a.Length
{
    forall i :: low <= i< high-1 ==> a[i]<= a[i+1]
}

predicate SortedExcept(a:array<int>, low:int, high:int, except:int) 
    reads a 
    // index must not out of bound 
    requires 0     <= low  <= except 
    requires except<= high < a.Length
{

    Sorted(a,low,except -1) && 
    Sorted(a, except+1, high) &&
    // if except is devided the array, then divided part can
    //  be connected as sorted
    (except != 0 && except != a.Length-1 ) ==> a[except -1] <= a[except +1]
}


method Swap(arr: array<int>, a:int, b:int)
    modifies arr
    // index protect 
    requires 0 <= a < arr.Length
    requires 0 <= b < arr.Length

    ensures arr[a] == old(arr[b])
    ensures arr[b] == old(arr[a])
{
    // proof the predicate better
    var tmp := arr[b];
    arr[b] := arr[a];
    arr[a] := tmp;
}

function MultisetExcept(arr: array<int>, index:int): multiset<int> 
    reads arr 
    requires arr.Length>=2
{
    if(index <= 0) then 
        multiset(arr[1..])
    else if (index >= arr.Length -1) then 
        multiset(arr[.. arr.Length -2])
    else 
        multiset(arr[..index - 1]+ arr[index+1..])
}

method shiftRight(arr: array<int>, start:int, end:int)
    modifies arr
    // arr size minimun 
    requires arr.Length >=2
    // basic index protect 
    requires 0<= start < arr.Length
    requires 0<= end < arr.Length
    // result expect 
    ensures end - start>0 ==>  arr[start+1..end] == old(arr[start..end-1])
{
    if(end - start <= 0){
        // break, because we can not shift 
        return;
    }
    // else if (end - start == 1){
    //     arr[end] := arr[start];
    // }
    else{
        var index := end;
        // while (index >= start + 1)
        //     decreases index
        //     invariant 
        // {
        //     arr[index] := arr[index -1];
        //     index:= index - 1;
        // }

        forall (i | start<=i <end) { arr[i+1]:= arr[i];}
    }
}

method InsertionSortShuffle(a: array<int>)  
 
    modifies a
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures multiset(a[..]) == multiset(old(a[..]));
    ensures Sorted(a, 0, a.Length)
{
    // storing the sorted end 
    var end:= 1;

    while ( end < a.Length)
        // loop will terminate 
        decreases a.Length - end 
        // match the @post of method 
        invariant multiset(a[..]) == multiset(old(a[..]));
        invariant Sorted(a, 0, end)

    {
        // pick the card out 
        var injectPoint := 0;
        var injectValue := a[end];

        while(
            // injectPoint is in index bound
            injectPoint < end && 
            // injectPoint is the point we want to inject 
            a[injectPoint] < injectValue
        )
            decreases end - injectPoint
            invariant 0 <= injectPoint < a.Length
        {
            injectPoint := injectPoint + 1;
        }
        // IMPLIES: a[injectPoint] >= injectValue
        // THEN: shift the array[injectPoint..end-1] right for 1 
        shiftRight(a, injectPoint, end-1);

        a[injectPoint] := injectValue;
        end := end + 1;
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