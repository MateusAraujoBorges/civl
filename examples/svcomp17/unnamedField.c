typedef struct qstr{
  union {
    struct {
      int hash;
      int len;
    };
    int hash_len;
  };
  unsigned char* name;
} qstr;

int main(){
  qstr q1;

  q1.name=(unsigned char*)0;
}
