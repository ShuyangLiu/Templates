/*
    Starter code for assignment 6, CSC 2/454, Fall 2016

    Provides skeleton of code for a simple hierarchy of set
    abstractions.

    Everything but /main/ should be moved to a .h file, which should
    then be #included from here.
*/

#include <set>
#include <iostream>
#include <string.h>
#include <type_traits>
#include <math.h>
using std::set;
using std::cout;
using std::string;

// Naive comparator.
// Provides a default for any type that has an operator<
// and an operator==.
//
template<typename T>
class comp {
public:
    bool precedes(const T& a, const T& b) const {
        return a<b;
    }
    bool equals(const T& a, const T& b) const {
        return a==b;
    }
};

// Abstract base class from which all sets are derived.
//
template<typename T, typename C = comp<T>>
class simple_set {
public:
    virtual ~simple_set<T, C>() { }
    // destructor should be virtual so that we call the right
    // version when saying, e.g.,
    // simple_set* S = new derived_set(args);
    //  ...
    // delete S;
    virtual simple_set<T, C>& operator+=(const T item) = 0;
    // inserts item into set
    // returns a ref so you can say, e.g.
    // S += a += b += c;
    virtual simple_set<T, C>& operator-=(const T item) = 0;
    // removes item from set, if it was there (otherwise does nothing)
    virtual bool contains(const T& item) const = 0;
    // indicates whether item is in set
};

//---------------------------------------------------------------

// Example of a set that implements the simple_set interface.
// Borrows the balanced tree implementation of the standard template
// library.  Note that you are NOT to use any standard library
// collections in your code (though you may use strings and streams).
//
template<typename T>
class std_simple_set : public virtual simple_set<T>, protected set<T> {
    // 'virtual' on simple_set ensures single copy if multiply inherited
public:
    virtual ~std_simple_set<T>() { }  // will invoke std::~set<T>()
    virtual std_simple_set<T>& operator+=(const T item) {
        set<T>::insert(item);
        return *this;
    }
    virtual std_simple_set<T>& operator-=(const T item) {
        (void) set<T>::erase(item);
        return *this;
    }
    virtual bool contains(const T& item) const {
        return (set<T>::find(item) != set<T>::end());
    }
};

//---------------------------------------------------------------

// Characteristic array implementation of set.
// Requires instantiation with guaranteed low and one-more-than-high
// bounds on elements that can be placed  in the set.  Should compile
// and run correctly for any element class T that can be cast to int.
// Throws out_of_bounds exception when appropriate.
//
class out_of_bounds { };    // exception
template<typename T>
class carray_simple_set : public virtual simple_set<T> {
    // 'virtual' on simple_set ensures single copy if multiply inherited
    const T L;
    const T H;
    bool* ptr;
    static const out_of_bounds err;
public:
    carray_simple_set(const T l, const T h) : L(l), H(h) {   // constructor
        if (l > h) throw err;
        ptr = new bool[H-L];
    }
    virtual ~carray_simple_set() {              // destructor
        delete &L;
        delete &H;
    }
    virtual carray_simple_set<T>& operator+=(const T item) {
        if( (item >= H) || (item < L)) throw err;
        //array[item-L] = item;
        *(ptr+((int)item-(int)L)) = true;
        return *this;
    }
    virtual carray_simple_set<T>& operator-=(const T item) {
        if( (item >= H) || (item < L)) throw err;
        *(ptr+((int)item-(int)L)) = false;
        return *this;
    }
    virtual bool contains(const T& item) const {
        return *(ptr+((int)item-(int)L)) == true;
    }
};

//---------------------------------------------------------------

// Naive hash function object.
// Provides a default for any type that can be cast to int.
//
template<typename T>
class cast_to_int {
public:
    int operator()(const T n) {
        return (int) n;
    }
};

// Hash table implementation of set.
// Requires instantiation with guaranteed upper bound on number of elements
// that may be placed in set.  Throws overflow if bound is exceeded.
// Can be instantiated without second generic parameter if element type
// can be cast to int; otherwise requires hash function object.
//
class overflow { };         // exception
template<typename T, typename F = cast_to_int<T>>
class hashed_simple_set : public virtual simple_set<T> {
    // 'virtual' on simple_set ensures single copy if multiply inherited
    // I recommend you pick a hash table size p that is a prime
    // number >= n, use F(e) % p as your hash function, and rehash
    // with kF(e) % p after the kth collision.  (But make sure that
    // F(e) is never 0.)
    int H;
    int P;
    T *ptr;
    static const overflow err;
public:
    hashed_simple_set(const int n) : H(n), P(prime_greater_than(n)){    // constructor
        // replace this line:
        //(void) n;
        //P = prime_greater_than(n); //table size
        ptr = new T[P];
    }
    virtual ~hashed_simple_set() { }    // destructor
    virtual hashed_simple_set<T, F>& operator+=(const T item) {
        // replace this line:
        //(void) item; 
        int s;
        if((F()(item) % H) == 0){
            s = 1;
        } else {
            s = F()(item) % H;
        }
        if((*(ptr+s) != item) && (*(ptr+s) != ((T) 0)))
        {
            //collision
            int k = 1;
            while(*(ptr+k*s) != item && *(ptr+k*s) != ((T) 0) && k<=H){
                k++;
            }
            if(k > H){
                throw err;
            }
            else{
                *(ptr+k*s) = item;
            }
        }
        else{
            *(ptr+s) = item;
        }
        return *this;
    }
    virtual hashed_simple_set<T, F>& operator-=(const T item) {
        // replace this line:
        //(void) item; 

        for (int k=1; k <= P; k++)
        {
            if((*(ptr+k*(F()(item) % H))) == item)
            {
                (*(ptr+k*(F()(item) % H))) = (T) 0;
                return *this;
            }
        }
        return *this;
    }
    virtual bool contains(const T& item) const {
        // replace this line:
        //(void) item;  
        int s = (F()(item) % H);
        if(s == 0) {
            s = 1;
        }
        for (int k=1; k <= P; k++)
        {
            if((*(ptr+k*s)) == item)
            {
                return true;
            }
        }
        return false;
    }
private:
    int isPrime(int num) {
        if (num == 1){
            return false;
        }
        if (num == 2){
            return true;
        }
        int bound = (int) floor(sqrt (num));
        for (int i=2; i<=bound; i++){
            //return false if num % n == 0
            if(num % i == 0){
                return false;
            }
        }
        return true;
    }

    int prime_greater_than(int n)
    {
        for(int i=n; i<n*n; i++)
        {
            if(isPrime(i))
            {
                return i;
            }
        }
        return 0;
    }
};

//---------------------------------------------------------------


// Sorted array implementation of set; supports binary search.
// Requires instantiation with guaranteed upper bound on number of
// elements that may be placed in set.  Throws overflow if bound is
// exceeded.
//
template<typename T, typename C = comp<T>>
class bin_search_simple_set : public virtual simple_set<T> {
    // 'virtual' on simple_set ensures single copy if multiply inherited
    // You'll need some data members here.
private:
    const T max;
    int current_size;
    C comparitor;
    int *a;
    static const overflow err;
    
    int find_mid_index(int upper_bound, int lower_bound) const {
        return ((upper_bound - lower_bound)/2 + lower_bound);
    }
    
    bool has_value(int upper, int lower, const T& item) const {
        if(upper <= lower) return false;
        else {
            int mid = find_mid_index(upper, lower);
            if(comparitor.equals(a[mid], item)) return true;
            else if(comparitor.precedes(a[mid], item)) { 
		if (mid==lower) return false;
		else { return has_value(upper, mid, item); }
            }
            else if(comparitor.precedes(item, a[mid])) {
           	if (mid == upper) return false;
                else { return has_value(mid, lower, item); }
 	    }
            return false;
        }
    }
public:
    // and some methods
    bin_search_simple_set(const T n): max(n), current_size(0), a(new T[max]), comparitor() {
        //constructor
    }

    virtual ~bin_search_simple_set(){
    }

    virtual bin_search_simple_set<T, C>& operator+=(const T item) {
	if(current_size >= max) throw err;
        if(comparitor.precedes(a[current_size - 1], item)) { a[current_size] = item; current_size++; }
        else {
            bool shift_array = false;
            int insert_index = 0;
            for(int i = 0; i < current_size; i++) {
                if(comparitor.equals(a[i], item)) break; // Does not accept equal values.
                else if(comparitor.precedes(item, a[i])) { shift_array = true; insert_index = i; break; }
            }
            if (shift_array) {
		    T val_to_enter = item;
		    for(int i = insert_index; i <= current_size; i++) {
			T current_a_i = a[i];
			a[i] = val_to_enter;
			val_to_enter = current_a_i;
		    }
                    current_size++;
            }
        }
        return *this;
    }

    virtual bin_search_simple_set<T>& operator-=(const T item) {
        if (current_size == 0) return *this;
        bool shift_array = false;
        int delete_index = 0;
        for(int i = 0; i < current_size; i++) {
            if(comparitor.equals(a[i], item)) { 
                shift_array = true; 
                delete_index = i; 
                break; 
            }
        }
        if (shift_array) {
	    for(int i = delete_index; i < current_size ; i++) {
         	a[i] = a[i + 1];
	    }
	    current_size--;
        }
	    
        return *this;
    }

    virtual bool contains(const T& item) const {
        return has_value(current_size, 0, item);
    }


};

//===============================================================
// RANGE SETS

// Function object for incrementing.
// Provides a default for any integral type.
//
template<typename T>
class increment {
    //static_assert(std::is_integral<T>::value, "Integral type required.");
public:
    T operator()(const T a)  {
        return (T)(((int)a)+1);
    }
};

// Range type.  Uses comp<T> by default, but you can provide your
// own replacement if you want, e.g. for C strings.
//
class empty_range { };      // exception
class merge_fail { };
class split_fail { };
template<typename T, typename C = comp<T>>
class range {
    const T L;      // represents all elements from L
    const bool Lc;  // inclusive?
    const T H;      // through H
    const bool Hc;  // inclusive?
    const C cmp;    // can't be static; needs explicit instantiation
    static const empty_range err;
    static const merge_fail merge_err;
    static const split_fail split_err;
public:
    range(const T l, const bool lc, const T h, const bool hc)
            : L(l), Lc(lc), H(h), Hc(hc), cmp() {
        if (cmp.precedes(h, l) || (cmp.equals(l, h) && (!Lc || !Hc))) throw err;
    }
    // no destructor needed
    T low() const { return L; }
    bool closed_low() const { return Lc; }
    T high() const { return H; }
    bool closed_high() const {return Hc; }
    bool contains(const T& item) const {
        return ((cmp.precedes(L, item) || (Lc && cmp.equals(L, item)))
                && (cmp.precedes(item, H) || (Hc && cmp.equals(item, H))));
    }
    // You may also find it useful to define the following:
    // bool precedes(const range<T, C>& other) const { ...
    bool overlaps(const range<T, C>& other) const { 
    	if((cmp.precedes(L, other.L) && cmp.precedes(other.L, H)) || 
    		(cmp.precedes(L, other.H) && cmp.precedes(other.H, H))) {
    		return true;
    	} else {
    		if (((cmp.equals(L, other.H)) && (Lc == true) && (other.Hc == true)) || 
    			((cmp.equals(H, other.L)) && (Hc == true) && (other.Lc == true))) {
    			return true;
    		} else {
    			return false;
    		}
    	}
    }

    range merge(const range<T, C>& other) const {
    	if(!overlaps(other)){
    		throw merge_err;
    	} else {
    		T l; T h; bool lc; bool hc; 
    		if (cmp.precedes(L, other.L)){
    			l = L;
    			lc = Lc;
    		} else {
    			l = other.L;
    			lc = other.Lc;
    		}

    		if (cmp.precedes(other.H, H)){
    			h = H;
    			hc = Hc;
    		} else {
    			h = other.H;
    			hc = other.Hc;
    		}
    		return range<T>(l, lc, h, hc);
    	}
    }

    range* split(const range<T, C>& other) const {
    	//split the range into 2 by another range
    	range ary [2]; 
    	if (cmp.precedes(other.L, L) || cmp.precedes(H, other.H)){
    		throw split_err;
    	} else {
    		T l1 = L;
    		T h1 = other.L;
    		bool lc1 = Lc;
    		bool hc1 = other.Lc;
    		ary[0] = range<T>(l1, lc1, h1, hc1);

    		T l2 = other.H;
    		T h2 = H;
    		bool lc2 = other.Hc;
    		bool hc2 = Hc;
    		ary[1] = range<T>(l2, lc2, h2, hc2);
    	}
    	return ary;
    }

    range* split(const T item) const {
    	range ary [2]; 
    	if (cmp.precedes(item, L) || cmp.precedes(H, item)){
    		throw split_err;
    	} else {
    		T l1 = L;
    		T h1 = item;
    		bool lc1 = Lc;
    		bool hc1 = false;
    		ary[0] = range<T>(l1, lc1, h1, hc1);

    		T l2 = item;
    		T h2 = H;
    		bool lc2 = false;
    		bool hc2 = Hc;
    		ary[1] = range<T>(l2, lc2, h2, hc2);
    	}

    	return ary;
    }
};

// You may find it useful to define derived types with two-argument
// constructors that embody the four possible combinations of open and
// close-ended:
//
// template<typename T, typename C = comp<T>>
// class CCrange : public range<T, C> { ...
//
// template<typename T, typename C = comp<T>>
// class COrange : public range<T, C> { ...
//
// template<typename T, typename C = comp<T>>
// class OCrange : public range<T, C> { ...
//
// template<typename T, typename C = comp<T>>
// class OOrange : public range<T, C> { ...

// This is the abstract class from which all range-supporting sets are derived.
//
template<typename T, typename C = comp<T>>
class range_set : public virtual simple_set<T> {
    // 'virtual' on simple_set ensures single copy if multiply inherited
public:
    virtual range_set<T>& operator+=(const range<T, C> r) = 0;
    virtual range_set<T>& operator-=(const range<T, C> r) = 0;
};

//---------------------------------------------------------------

// As implemented in the standard library, sets contain individual
// elements, not ranges.  (There are range insert and erase operators, but
// (a) they use iterators, (b) they take time proportional to the number of
// elements in the range, and (c) they require, for deletion, that the
// endpoints of the range actually be in the set.  An std_range_set, as
// defined here, avoids shortcomings (a) and (c), but not (b).  Your
// bin_search_range_set should avoid (b), though it will have slow insert
// and remove operations.  A tree_range_set (search tree -- extra credit)
// would have amortized log-time insert and remove for individual elements
// _and_ ranges.
//
template<typename T, typename C = comp<T>, typename I = increment<T>>
class std_range_set : public virtual range_set<T, C>, public std_simple_set<T> {
    // 'virtual' on range_set ensures single copy if multiply inherited
    static_assert(std::is_integral<T>::value, "Integral type required.");
    I inc;
public:
    // The first three methods below tell the compiler to use the
    // versions of the simple_set methods already found in std_simple_set
    // (given true multiple inheritance it can't be sure it should do that
    // unless we tell it).
    virtual std_simple_set<T>& operator+=(const T item) {
        return std_simple_set<T>::operator+=(item);
    }
    virtual std_simple_set<T>& operator-=(const T item) {
        return std_simple_set<T>::operator-=(item);
    }
    virtual bool contains(const T& item) const {
        return std_simple_set<T>::contains(item);
    }
    virtual range_set<T>& operator+=(const range<T, C> r) {
        for (T i = (r.closed_low() ? r.low() : inc(r.low()));
             r.contains(i); i = inc(i)) {
            *this += i;
        }
        return *this;
    }
    virtual range_set<T>& operator-=(const range<T, C> r) {
        for (T i = (r.closed_low() ? r.low() : inc(r.low()));
             r.contains(i); i = inc(i)) {
            *this -= i;
        }
        return *this;
    }
};

//---------------------------------------------------------------

// insert an appropriate carray_range_set declaration here

template<typename T, typename C = comp<T>, typename I = increment<T>>
class carray_range_set : public virtual range_set<T, C>, protected carray_simple_set<T>{
    // 'virtual' on range_set ensures single copy if multiply inherited
    //static_assert(std::is_integral<T>::value, "Integral type required.");
    I inc;
    C cmp;
public:
    carray_range_set(const T l, const T h) : carray_simple_set<T>(l, h), cmp(), inc() {}

    virtual carray_simple_set<T>& operator+=(const T item){
        return carray_simple_set<T>::operator+=(item);
    }

    virtual carray_simple_set<T>& operator-=(const T item){
        return carray_simple_set<T>::operator-=(item);
    }

    virtual range_set<T>& operator+=(const range<T, C> r) {
        for (T i = (r.closed_low() ? r.low() : inc(r.low())); r.contains(i); i = inc(i)) {
            *this += i;
        }
        return *this;
    }

    virtual range_set<T>& operator-=(const range<T, C> r) {
        for (T i = (r.closed_low() ? r.low() : inc(r.low()));
             r.contains(i); i = inc(i)) {
            *this -= i;
        }
        return *this;
    }

    virtual bool contains(const T& item) const {
        return carray_simple_set<T>::contains(item);
    }
};

//---------------------------------------------------------------

// insert an appropriate hashed_range_set declaration here
template<typename T, typename F = cast_to_int<T>, typename C = comp<T>, typename I = increment<T>>
class hashed_range_set : public virtual range_set<T, C>, public hashed_simple_set<T, F>{
	I inc;
    C cmp;
public:
	hashed_range_set(const int num) : hashed_simple_set<T, F>(num), cmp(), inc() {
	}
	virtual hashed_simple_set<T>& operator+=(const T item){
		return hashed_simple_set<T>::operator+=(item);
	}
	virtual hashed_simple_set<T>& operator-=(const T item){
		return hashed_simple_set<T>::operator-=(item);
	}
	virtual bool contains(const T& item) const {
        return hashed_simple_set<T>::contains(item);
    }
    virtual hashed_range_set<T>& operator+=(const range<T, C> r) {
        for (T i = (r.closed_low() ? r.low() : inc(r.low())); r.contains(i); i = inc(i)) {
            *this += i;
        }
        return *this;
    }
    virtual hashed_range_set<T>& operator-=(const range<T, C> r) {
        for (T i = (r.closed_low() ? r.low() : inc(r.low()));
             r.contains(i); i = inc(i)) {
            *this -= i;
        }
        return *this;
    }

};
//---------------------------------------------------------------

// insert an appropriate bin_search_range_set declaration here

//===============================================================

// comparator for C strings
//
class lexico_less {
public:
    bool precedes(const char *a, const char *b) const {
        return strcmp(a, b) < 0;
    }
    bool equals(const char *a, const char *b) const {
        return strcmp(a, b) == 0;
    }
};

typedef enum{mon, tue, wed, thu, fri} weekday;

int main() {

    // Some miscellaneous code to get you started on testing your sets.
    // The following should work:

    std_simple_set<int> R;
    R += 3;
    cout << "3 is " << (R.contains(3) ? "" : "not ") << "in R\n";
    cout << "5 is " << (R.contains(5) ? "" : "not ") << "in R\n";

    simple_set<double>* S = new std_simple_set<double>();
    *S += 3.14;
    cout << "pi is " << (S->contains(3.14) ? "" : "not ") << "in S\n";
    cout << "e is " << (S->contains(2.718) ? "" : "not ") << "in S\n";

    std_simple_set<string> U;
    U += "hello";
    cout << "\"hello\" is " << (U.contains("hello") ? "" : "not ") << "in U\n";
    cout << "\"foo\" is " << (U.contains("foo") ? "" : "not ") << "in U\n";

    // simple_set<weekday>* V = new carray_simple_set<weekday>(mon, (weekday)5);
    // *V += tue;
    // *V += wed;
    // *V -= wed;
    // cout << "tue is " << (V->contains(tue)? "" : "not ") << "in V\n";
    // cout << "wed is " << (V->contains(wed)? "" : "not ") << "in V\n";

    //range_set<weekday>* V_r = new hashed_range_set<weekday>(6);
    hashed_range_set<weekday, cast_to_int<weekday>> V_r(6);
    V_r += range<weekday>(mon, true, wed, true);
    cout << "mon is " << (V_r.contains(mon)? "" : "not ") << "in V_r\n";
    cout << "tue is " << (V_r.contains(tue)? "" : "not ") << "in V_r\n";
    cout << "wed is " << (V_r.contains(wed)? "" : "not ") << "in V_r\n";
    cout << "thu is " << (V_r.contains(thu)? "" : "not ") << "in V_r\n";
    cout << "fri is " << (V_r.contains(fri)? "" : "not ") << "in V_r\n";
    cout << "\n";

    range_set<int>* X = new carray_range_set<int>(0, 100);
    *X += range<int>(5, true, 8, false);
    if (X->contains(4)) cout << "4 is in X\n";
    if (X->contains(5)) cout << "5 is in X\n";      // should print
    if (X->contains(6)) cout << "6 is in X\n";      // should print
    if (X->contains(7)) cout << "7 is in X\n";      // should print
    if (X->contains(8)) cout << "8 is in X\n";
    if (X->contains(9)) cout << "9 is in X\n";
    *X -= range<int>(6, true, 10, false);
    if (X->contains(4)) cout << "4 is now in X\n";
    if (X->contains(5)) cout << "5 is now in X\n";      // should print
    if (X->contains(6)) cout << "6 is now in X\n";
    if (X->contains(7)) cout << "7 is now in X\n";
    if (X->contains(8)) cout << "8 is now in X\n";
    if (X->contains(9)) cout << "9 is now in X\n";

    // hashed_simple_set<weekday, cast_to_int<weekday>> H(5);
    // H += mon;
    // cout << "mon is " << (H.contains(mon)? "" : "not ") << "in H\n";
    // H += tue;
    // cout << "tue is " << (H.contains(tue)? "" : "not ") << "in H\n";
    // cout << "mon is " << (H.contains(mon)? "" : "not ") << "in H\n";
    // cout << "\n";



    //cout << std::is_integral<weekday>::value << std::endl;
/*
    hashed_simple_set<weekday, cast_to_int<weekday>> H(5);
    H += mon;
    cout << "mon is " << (H.contains(mon)? "" : "not ") << "in H\n";
    H += tue;
    //H -= 101;
    cout << "tue is " << (H.contains(tue)? "" : "not ") << "in H\n";
    cout << "mon is " << (H.contains(mon)? "" : "not ") << "in H\n";
    cout << "202 is " << (H.contains(202)? "" : "not ") << "in H\n";
    cout << "101 is " << (H.contains(101)? "" : "not ") << "in H\n";
*/
    cout << "\n";

    bin_search_simple_set<int> B(10);
    cout << "19 is " << (B.contains(19)? "" : "not ") << "in B\n";
    B += 20;
    B += 11;
    B += 10;
    B += 15;
    cout << "20 is " << (B.contains(20)? "" : "not ") << "in B\n";
    cout << "11 is " << (B.contains(11)? "" : "not ") << "in B\n";
    cout << "10 is " << (B.contains(10)? "" : "not ") << "in B\n";
    cout << "15 is " << (B.contains(15)? "" : "not ") << "in B\n";
    cout << "16 is " << (B.contains(16)? "" : "not ") << "in B\n";

    cout << "\n";

    B -= 11;
    B -= 15;

    cout << "20 is " << (B.contains(20)? "" : "not ") << "in B\n";
    cout << "11 is " << (B.contains(11)? "" : "not ") << "in B\n"; 
    cout << "10 is " << (B.contains(10)? "" : "not ") << "in B\n";
    cout << "15 is " << (B.contains(15)? "" : "not ") << "in B\n";

    cout << "\n"; 


/*
    range_set<weekday>* V_r = new carray_range_set<weekday>(mon, (weekday)5);
    *V_r += range<weekday>(mon, true, wed, true);
    cout << "mon is " << (V_r->contains(mon)? "" : "not ") << "in V_r\n";
    cout << "tue is " << (V_r->contains(tue)? "" : "not ") << "in V_r\n";
    cout << "wed is " << (V_r->contains(wed)? "" : "not ") << "in V_r\n";
    cout << "thu is " << (V_r->contains(thu)? "" : "not ") << "in V_r\n";
    cout << "fri is " << (V_r->contains(fri)? "" : "not ") << "in V_r\n";
    cout << "\n";
    *V_r += range<weekday>(tue, true, thu, false);
    cout << "mon is " << (V_r->contains(mon)? "" : "not ") << "in V_r\n";
    cout << "tue is " << (V_r->contains(tue)? "" : "not ") << "in V_r\n";
    cout << "wed is " << (V_r->contains(wed)? "" : "not ") << "in V_r\n";
    cout << "thu is " << (V_r->contains(thu)? "" : "not ") << "in V_r\n";
    cout << "fri is " << (V_r->contains(fri)? "" : "not ") << "in V_r\n";
    cout << "\n";
    *V_r -= range<weekday>(wed, true, fri, false);
    cout << "mon is " << (V_r->contains(mon)? "" : "not ") << "in V_r\n";
    cout << "tue is " << (V_r->contains(tue)? "" : "not ") << "in V_r\n";
    cout << "wed is " << (V_r->contains(wed)? "" : "not ") << "in V_r\n";
    cout << "thu is " << (V_r->contains(thu)? "" : "not ") << "in V_r\n";
    cout << "fri is " << (V_r->contains(fri)? "" : "not ") << "in V_r\n";
    cout << "\n";
*/
/*
    // B -= 500;
    // cout << "500 is " << (H.contains(500)? "" : "not ") << "in H\n";
    B += 5000;
    cout << "5000 is " << (B.contains(5000)? "" : "not ") << "in B\n";
    cout << "500 is " << (B.contains(500)? "" : "not ") << "in B\n";
*/
/*
    range<string> r1("a", true, "f", true);
    cout << "\"b\" is " << (r1.contains("b") ? "" : "not ") << "in r1\n";
    cout << "\"aaa\" is " << (r1.contains("aaa") ? "" : "not ") << "in r1\n";
    cout << "\"faa\" is " << (r1.contains("faa") ? "" : "not ") << "in r1\n";

    range<const char*, lexico_less> r2("a", true, "f", true);
    cout << "\"b\" is " << (r2.contains("b") ? "" : "not ") << "in r2\n";
    cout << "\"aaa\" is " << (r2.contains("aaa") ? "" : "not ") << "in r2\n";
    cout << "\"faa\" is " << (r2.contains("faa") ? "" : "not ") << "in r2\n";
    */

    // The following will not work correctly yet:
/*
    range_set<int>* X = new std_range_set<int>();
    *X += range<int>(5, true, 8, false);
    if (X->contains(4)) cout << "4 is in X\n";
    if (X->contains(5)) cout << "5 is in X\n";      // should print
    if (X->contains(6)) cout << "6 is in X\n";      // should print
    if (X->contains(7)) cout << "7 is in X\n";      // should print
    if (X->contains(8)) cout << "8 is in X\n";
    if (X->contains(9)) cout << "9 is in X\n";
    *X -= range<int>(6, true, 10, false);
    if (X->contains(4)) cout << "4 is now in X\n";
    if (X->contains(5)) cout << "5 is now in X\n";      // should print
    if (X->contains(6)) cout << "6 is now in X\n";
    if (X->contains(7)) cout << "7 is now in X\n";
    if (X->contains(8)) cout << "8 is now in X\n";
    if (X->contains(9)) cout << "9 is now in X\n";

    simple_set<weekday>* V = new carray_simple_set<weekday>(mon, (weekday)5);
	*V += tue;
	//cout << "tue is" << (V->contains(tue)? "" : "not ") << "in V\n";
    hashed_simple_set<int, cast_to_int<int>> H(100);

    bin_search_simple_set<double> J(100);
    */
}
