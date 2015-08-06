#include <iostream>
#include <string>

using namespace std;

class object1{
public:
	int a,b,c;
protected:
	object1():a(0),b(0),c(0){}
public:
	static object1* instance(){
		return (new object1());
	}

	void func(){
		int v1 = a + b;
		int v2 = a*b;
	}
};

int main(){
	object1 *obj = object1::instance();
	obj->func();
	return 0;
}
