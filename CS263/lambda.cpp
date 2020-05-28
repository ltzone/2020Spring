#include <functional>
#include <iostream>

template <typename T>
std::function<T(T)> do_it_three_times (std::function<T(T)> f) {
    return [f](T x) { return f(f(f(x))); };
}

int main() {
    std::function<int(int)> add_one = [](int x) {return x + 1; };
    std::function<int(int)> square = [](int x) {return x * x; };
    std::cout << do_it_three_times (add_one) (1);
    std::cout << std::endl;
    std::cout << do_it_three_times (square) (2);
    std::cout << std::endl;
    std::cout << do_it_three_times (do_it_three_times(add_one)) (0);
    std::cout << std::endl;
    // The following line does not work for C++,
    // because do_it_three_times is a function not an object
    // std::cout << do_it_three_times (do_it_three_times) (add_one) (0);
    std::function<std::function<int(int)>(std::function<int(int)>)>
      do_it_three_times_obj =
      [](std::function<int(int)> f) {return do_it_three_times (f); };
    std::cout << do_it_three_times (do_it_three_times_obj) (add_one) (0);
    std::cout << std::endl;
}