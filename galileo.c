/*
 * galileo.c: static analysis tool for geometry attacks
 * Copyright (C) 2006, 2007, 2022 Hovav Shacham
 *
 * All rights reserved.  Do not redistribute.
 */


#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <libelf.h>
#include "riscv-disas.h"

/* from stevens. */
#define	MAXLINE		4096	/* max text line length */

#define ERR_DO_ERRNO 1
#define ERR_DO_ELF 2

static void
err_doit(int errnoflag, const char *fmt, va_list ap)
{
  int errno_save, n;
  char buf[MAXLINE];

  errno_save = errno;		/* value caller might want printed */
  vsnprintf(buf, sizeof(buf), fmt, ap);	/* this is safe */
  n = strlen(buf);
  if (errnoflag == ERR_DO_ERRNO)
    snprintf(buf+n, sizeof(buf)-n, ": %s", strerror(errno_save));
  else if (errnoflag == ERR_DO_ELF)
    snprintf(buf+n, sizeof(buf)-n, ": %s", elf_errmsg(elf_errno()));
  strcat(buf, "\n");

  fflush(stdout);         /* in case stdout and stderr are the same */
  fputs(buf, stderr);
  fflush(stderr);

  return;
}

static void
err_sys(const char *fmt, ...)
{
  va_list ap;

  va_start(ap, fmt);
  err_doit(ERR_DO_ERRNO, fmt, ap);
  va_end(ap);
  exit(1);
}

static void
err_elf(const char *fmt, ...)
{
  va_list ap;

  va_start(ap, fmt);
  err_doit(ERR_DO_ELF, fmt, ap);
  va_end(ap);
  exit(1);
}

static void
err_quit(const char *fmt, ...)
{
  va_list ap;

  va_start(ap, fmt);
  err_doit(0, fmt, ap);
  va_end(ap);
  exit(1);
}

char *
Strdup(const char *str)
{
  char	*ptr;

  if ( (ptr = strdup(str)) == NULL)
    err_sys("strdup error");
  return(ptr);
}

/* end stevens */


struct elf_fn
{
  char *name;
  size_t offset;
  size_t len;
};

static int
elf_fn_compare(const void *ap, const void *bp)
{
  size_t a_offset, b_offset;

  a_offset = ((struct elf_fn *)ap)->offset;
  b_offset = ((struct elf_fn *)bp)->offset;

  if (a_offset < b_offset)
    return -1;
  if (a_offset == b_offset)
    return 0;
  return +1;
}

static int
elf_fn_compare_len_bounded(const void *ap, const void *bp)
{
  size_t key_addr, offset, len;

  key_addr = ((struct elf_fn *)ap)->offset;
  offset = ((struct elf_fn *)bp)->offset;
  len = ((struct elf_fn *)bp)->len;

  if (key_addr < offset)
    return -1;
  if (key_addr < offset+len)
    return 0;
  return +1;
}

static void *libc = NULL;
static size_t libc_len = 0;     /* file size */
static size_t libc_start = 0;   /* start of .text */
static size_t libc_stop = 0;    /* end of .text */

/* libc_fns has n_libc_fns entries, sorted by offset */
static int n_libc_fns = 0;
static struct elf_fn *libc_fns = NULL;

struct elf_fn *
blame_libc_fn(size_t addr)
{
  struct elf_fn key;
  key.offset = addr;

  return bsearch(&key, libc_fns, n_libc_fns,
                 sizeof(struct elf_fn), elf_fn_compare_len_bounded);
}

void
elf_read_libc(int fd)
{
  Elf *elf;
  Elf64_Ehdr *ehdr;
  Elf64_Phdr *phdr;

  Elf_Scn *scn, *str_scn;
  Elf64_Shdr *shdr;

  int str_link;
  Elf_Data *symdata, *strdata;
  int nsyms;

  Elf64_Sym *symarr;
  char *strs;

  int i;

  if (elf_version(EV_CURRENT) == EV_NONE)
    err_elf("Cannot set ELF version");
  if ( (elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
    err_elf("Cannot begin ELF reading");

  if ( (ehdr = elf64_getehdr(elf)) == NULL)
    err_elf("Cannot get eheader");
  if ( (phdr = elf64_getphdr(elf)) == NULL)
    err_elf("Cannot get pheader");

  for (i = 0; i < ehdr->e_phnum; i++)
    if (phdr[i].p_type == PT_LOAD
        && (phdr[i].p_flags & PF_X) != 0)
      break;
  if (i == ehdr->e_phnum)
    err_quit("Can't find text segment");

  libc_start = phdr[i].p_offset;
  libc_stop = phdr[i].p_offset + phdr[i].p_filesz;

  for (scn = NULL, shdr = NULL, i = 0; i < ehdr->e_shnum; i++)
    {
      if ( (scn = elf_getscn(elf, i)) == NULL)
        err_elf("Cannot get section %d", i);
      if ( (shdr = elf64_getshdr(scn)) == NULL)
        err_elf("Cannot get section  header %d", i);
      
      if (shdr->sh_type == SHT_DYNSYM)
        break;
    }
  if (i == ehdr->e_shnum)
    err_quit("DYNSYM section not found");

  if ( (str_link = shdr->sh_link) == 0)
    err_quit("No string section associated with DYNSYM section");
  if ( (str_scn = elf_getscn(elf, str_link)) == NULL)
    err_elf("Cannot get string section %d", str_link);

  if ( (symdata = elf_getdata(scn, NULL)) == NULL)
    err_elf("No data associated with DYNSYM");
  if ( (strdata = elf_getdata(str_scn, NULL)) == NULL)
    err_elf("No data associated with string table");

  nsyms = symdata->d_size / sizeof(Elf64_Sym);
  symarr = (Elf64_Sym *)symdata->d_buf;
  strs = strdata->d_buf;

  /* for convenience in some analyses, we'll also allocate
   * two guard entries in libc_fns ... */

  if ( (libc_fns = malloc((nsyms+2) * sizeof(struct elf_fn)))
       == NULL)
    err_quit("Memory exhausted in malloc");

  /* skip past first entry for now */
  libc_fns++;

  for (n_libc_fns = i = 0; i < nsyms; i++)
    {
      if (ELF64_ST_TYPE(symarr[i].st_info) != STT_FUNC)
        continue;
      libc_fns[n_libc_fns].name
        = Strdup(strs + symarr[i].st_name);
      libc_fns[n_libc_fns].offset = symarr[i].st_value;
      libc_fns[n_libc_fns].len = symarr[i].st_size;
      n_libc_fns++;
    }

  qsort(libc_fns, n_libc_fns, sizeof(struct elf_fn),
        elf_fn_compare);

  /* guard entries: first and last dummies */
  libc_fns[-1].name = "dummy:start";
  libc_fns[-1].offset = libc_start;
  libc_fns[-1].len = 0;
  libc_fns[n_libc_fns].name = "dummy:stop";
  libc_fns[n_libc_fns].offset = libc_stop;
  libc_fns[n_libc_fns].len = 0;

  elf_end(elf);
}

void
map_libc(char *libc_file)
{
  int fd;
  struct stat sb;
  void *addr;

  if ( (fd = open(libc_file, O_RDONLY, 0)) < 0)
    err_sys("Cannot open libc");
  
  if (fstat(fd, &sb) < 0)
    err_sys("Cannot stat libc");

  if ( (addr = mmap(NULL, sb.st_size, PROT_READ, MAP_SHARED, fd, 0))
       == (void *)-1)
    err_sys("Cannot map libc");

  libc = addr;
  libc_len = sb.st_size;

  elf_read_libc(fd);
}

struct insn_node
{
  rv_inst inst;
  rv_decode dec;

  int count;

  struct insn_node **children;
  int c_size;
  int c_used;

  struct insn_node *parent;
};

static int
node_compare(const void *ap, const void *bp)
{
  struct insn_node *a, *b;

  a = *(struct insn_node **)ap;
  b = *(struct insn_node **)bp;

 return a->count - b->count; 
}

static void
print_insn_loc(size_t addr)
{
  struct elf_fn *fn = blame_libc_fn(addr);

  if (fn != NULL)
    printf("@0x%lx in %s", addr, fn->name);
  else
    printf("@0x%lx", addr);
}

static void
print_insn_bytes(rv_inst inst)
{
  switch (inst_length(inst))
    {
    case 2:
      printf("%02lx %02lx",
             inst         & 0xff, (inst >> 8)  & 0xff);
      break;
    case 4:
      printf("%02lx %02lx %02lx %02lx",
             inst         & 0xff, (inst >> 8)  & 0xff,
             (inst >> 16) & 0xff, (inst >> 24) & 0xff);
      break;
    default:
      err_quit("Unsupported instruction length %uld", inst_length(inst));
      break;
    }
}

/* runtime options */

static int max_depth = -1;       /* -1 means unlimited */
static int print_counts = 1;
static int print_locs = 1;
static int print_bytes = 1;

static void
walk_tree_and_print(struct insn_node *node, int level)
{
  int i;
  char decbuf[128];

  if (node->children != NULL &&
      (max_depth == -1 || level < max_depth))
    {
      /* prettify ordering */
      qsort(node->children, node->c_used,
            sizeof(struct insn_node *), node_compare);
      for (i = 0; i < node->c_used; i++)
        walk_tree_and_print(node->children[i], level+1);
    }

  printf("%*s", 2*level, "");
  if (print_counts)
    {
      printf("%dx", node->count);
    }
  if (print_locs)
    {
      if (print_counts)
        printf(" ");
      printf("(e.g., ");
      print_insn_loc(node->dec.pc);
      printf(")");
    }
  if (print_bytes)
    {
      if (print_counts || print_locs)
        printf("\t");
      print_insn_bytes(node->inst);
    }
  format_decoded_inst(decbuf, 128, &node->dec);
  if (print_counts || print_locs || print_bytes)
    printf("\t");
  printf("%s\n", decbuf);
}

static void
usage(void)
{
  fprintf(stderr,
          "Usage: galileo [-c] [-l] [-b] [-d <depth>] <libc>\n");
  exit(EXIT_FAILURE);
}

static char *
parse_args(int argc, char *argv[])
{
  int opt;
  while ( (opt = getopt(argc, argv, "clbd:")) != -1)
    {
      switch(opt)
        {
        case 'c':
          print_counts = 0;
          break;
        case 'l':
          print_locs = 0;
          break;
        case 'b':
          print_bytes = 0;
          break;
        case 'd':
          max_depth = atoi(optarg);
          break;
        default:
          usage();
        }
    }

  if (optind != argc-1)
    usage();

  return argv[optind];
}

struct insn_node *
add_node_child(struct insn_node *node, rv_inst inst, size_t offset)
{
  struct insn_node *child;

  if (node->children == NULL)
    {
      node->c_size = 4;
      node->children = malloc(node->c_size
                              * sizeof(struct insn_node *));
      if (node->children == NULL)
        err_quit("Memory exhausted in malloc");
      node->c_used = 0;
    }

  if (node->c_used == node->c_size)
    {
      node->c_size *= 2;
      node->children = realloc(node->children,
                               node->c_size 
                                 * sizeof(struct insn_node *));
      if (node->children == NULL)
        err_quit("Memory exhausted in realloc");
    }

  child = malloc(sizeof(struct insn_node));
  if (child == NULL)
    err_quit("Memory exhausted in malloc");
  child->inst = inst;
  decode_inst(&child->dec, rv64, offset, inst);
  child->count = 1;
  child->children = NULL;
  child->c_size = child->c_used = 0;

  child->parent = node;

  node->children[node->c_used++] = child;

  return child;
}

struct insn_node *
make_root(size_t offset)
{
  struct insn_node *root;
  size_t inst_len;

  root = malloc(sizeof(struct insn_node));
  if (root == NULL)
    err_quit("Memory exhausted in malloc");

  fetch_inst(libc+offset, &root->inst, &inst_len);
  decode_inst(&root->dec, rv64, offset, root->inst);
  root->count = 0;
  root->children = NULL;
  root->c_size = root->c_used = 0;

  root->parent = NULL;
  
  return root;
}

/* add if not already present.  return point regardless. */

struct insn_node *
maybe_add_node_child(struct insn_node *node, rv_inst inst, size_t offset)
{
  int i;

  if (node->children == NULL)
    return add_node_child(node, inst, offset);

  for (i = 0; i < node->c_used; i++)
    if (node->children[i]->inst == inst)
      {
        node->children[i]->count++;
        return node->children[i];
      }

  return add_node_child(node, inst, offset);
}

/*
 * TODO: fill in `is_boring`.
 * 
 * A boring instruction is one not useful in ROP, for example because
 * it perturbs the program counter.  We have given a couple of
 * examples of boring instructions below; add the rest.  You will want
 * to refer to the `rv_op` enum in riscv-disas.h for the list of all
 * opcodes that `decode_inst` can return.
 */

int
is_boring(rv_inst inst, size_t offset)
{
  rv_decode dec;
  decode_inst(&dec, rv64, offset, inst);

  switch (dec.op) {
  case rv_op_illegal:           /* can't use an illegal insn in ROP! */
  /* TODO: another 30ish cases go here ... */
  /* jump instructions */
  case rv_op_jal:               /* jal will perturb pc, not useful */
  case rv_op_jalr:

  /* branch instructions */
  case rv_op_beq:
  case rv_op_bne:
  case rv_op_blt:
  case rv_op_bge:
  case rv_op_bltu:
  case rv_op_bgeu:

  /* environment instructions */
  case rv_op_ecall:
  case rv_op_ebreak:

  /* return instructions */
  case rv_op_uret:
  case rv_op_sret:
  case rv_op_hret:
  case rv_op_mret:
  case rv_op_dret:

  /* stalling instructions */
  case rv_op_wfi:

  /* compressed jump instructions */
  case rv_op_c_jal:
  case rv_op_c_j:
  case rv_op_c_jr:
  case rv_op_c_jalr:

  /* compressed branch instructions */
  case rv_op_c_beqz:
  case rv_op_c_bnez:

  /* compressed environment instructions */
  case rv_op_c_ebreak:

  /* more branch instructions */
  case rv_op_beqz:
  case rv_op_bnez:
  case rv_op_blez:
  case rv_op_bgez:
  case rv_op_bltz:
  case rv_op_bgtz:
  case rv_op_ble:
  case rv_op_bleu:
  case rv_op_bgt:
  case rv_op_bgtu:

  /* more jump instructions */
  case rv_op_j:
  case rv_op_ret:
  case rv_op_jr:
    return 1;	// boring.

  default:
    return 0;	// not boring by default
  }
}

/*
 * TODO: implement `disasm_back_from`.
 *
 * Pseudocode for `disasm_back_from` is given in Figure 33 of the
 * assigned ROP paper (where it is called BuildFrom).
 * 
 * Look at `do_insn_trie`, below, for inspiration.
 *
 * You will use the `fetch_inst` function from riscv-disas.h, along
 * with `maybe_add_node_child` and recursive call to
 * `disasm_back_from`.  Oh, and don't forget `is_boring`, which you
 * worked so hard to fill out!
 */
void
disasm_back_from(size_t offset, struct insn_node *node)
{
  size_t trylen;                /* look for an insn of this length */
  rv_inst inst;                 /* fetch_inst fills this variable */
  size_t inst_len;              /* ... and also this one */

  struct insn_node *child;      /* returned by maybe_add_node_child */
  rv_decode dec_inst;        /* decode_inst fills this variable */

  /* TODO: implement BuildFrom from Figure 33! */
  for (trylen = 2; trylen < 4; trylen += 2) {
    // fetch + decode instruction
    fetch_inst(libc+offset-trylen, &inst, &inst_len);
    decode_inst(&dec_inst, rv64, offset-trylen, inst);
    
    // if instruction is valid
    if (dec_inst.op != rv_op_illegal) {
      child = maybe_add_node_child(node, inst, offset-trylen); // add to the parent node
      if (is_boring(inst, offset-trylen) == 0){ // if insn isn't boring
        disasm_back_from(offset-trylen, child); // recursive call
      }
    }
  }
}

int
is_ret(rv_inst inst, size_t offset)
{
  rv_decode dec;
  decode_inst(&dec, rv64, offset, inst);

  return dec.op == rv_op_ret;
}

void
do_insn_trie(void)
{
  struct insn_node *root;
  size_t offset;
  rv_inst inst;
  size_t inst_len;

  /* make root node */
  for (offset = libc_start; offset < libc_stop; offset += 2)
    {
      fetch_inst(libc+offset, &inst, &inst_len);
      if (is_ret(inst, offset))
        break;
    }
  if (offset >= libc_stop)
    err_quit("No ret found");
  root = make_root(offset);

  for (offset = libc_start; offset < libc_stop; offset += 2)
    {
      fetch_inst(libc+offset, &inst, &inst_len);
      if (is_ret(inst, offset))
        {
          root->count++;
          disasm_back_from(offset, root);
        }
    }

  walk_tree_and_print(root, 0);
}

int
main(int argc, char *argv[])
{
  map_libc(parse_args(argc, argv));
  do_insn_trie();
  return 0;
}
