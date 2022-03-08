#include<cstdint>
#include<set>
#include<iostream>
#include<array>

int main(int argc, char** argv) {

  //std::cout << "You have entered " << argc
  //     << " arguments:" << "\n";
  
  //for (int i = 0; i < argc; ++i)
  //  std::cout << argv[i] << "\n";
  
  if (argc != 2)
    return 1;

  ///std::cout << "Yay1\n.";
  int n = std::strtoull(argv[1], NULL, 0);
  std::cout << n << "\n";

  int64_t random_data[n];
  for (int i = 0; i < n; i++)
    random_data[i] = rand();

  std::set<int64_t> set;
  for (int i = 0; i < n; i++) {
    //std::cout << random_data[i] << "\n";
    set.insert(random_data[i]);
  }

  // setOfNumbers.insert(2L);
  // setOfNumbers.insert(3L);
  // setOfNumbers.insert(4L);
  // // Only 3 elements will be inserted
  // std::cout<<"Set Size = "<<setOfNumbers.size()<<std::endl;
  // // Iterate through all the elements in a set and display the value.
  // for (std::set<std::int64_t>::iterator it=setOfNumbers.begin(); it!=setOfNumbers.end(); ++it)
  //     std::cout << ' ' << *it;
  // std::cout<<"\n";
  return 0;
}
