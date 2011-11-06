(* Loader for NaClVerifier. Copyright Jean-Baptiste Tristan. *)

let ei_nident = 16
type elf_half = Int64.t
type elf_word = Int64.t
type elf_addr = Int64.t
type elf_off = Int64.t

(* Watch out for endianess!!! *)
let read_n_bytes n chan =
  let rec read_n_aux n l =
    if n = 0 then l else read_n_aux (n-1) (input_byte chan :: l)
  in  
  read_n_aux n []
;;

let bytes_to_int64 l =
  let rec bytes_to_int l pos i = 
    match l with
      | [] -> i
      | b :: l -> bytes_to_int l (pos - 1) (Int64.add i (Int64.shift_left (Int64.of_int b) (pos * 8)))
  in
  bytes_to_int l (List.length l - 1) (Int64.zero)
;;

let convert_n_bytes n chan = bytes_to_int64 (read_n_bytes n chan)

(* The following four definitions must be changed depending on the architecture *)
let read_half chan = convert_n_bytes 2 chan 
let read_word chan = convert_n_bytes 4 chan
let read_addr chan = convert_n_bytes 4 chan
let read_off chan = convert_n_bytes 4 chan

type file_header = {
  e_ident: (int list);          (* Magic number and other info *)       
  e_type: elf_half;		(* Object file type *)
  e_machine: elf_half;		(* Architecture *)
  e_version: elf_word;		(* Object file version *)
  e_entry: elf_addr;		(* Entry point virtual address *)
  e_phoff: elf_off;		(* Program header table file offset *)
  e_shoff: elf_off;		(* Section header table file offset *)
  e_flags: elf_word;		(* Processor-specific flags *)
  e_ehsize: elf_half;		(* ELF header size in bytes *)
  e_phentsize: elf_half;	(* Program header table entry size *)
  e_phnum: elf_half;		(* Program header table entry count *)
  e_shentsize: elf_half;	(* Section header table entry size *)
  e_shnum: elf_half;		(* Section header table entry count *)
  e_shstrndx: elf_half;		(* Section header string table index *)
};;

let read_file_header chan : file_header =
  let e_ident = read_n_bytes ei_nident chan in
  let e_type = read_half chan in
  let e_machine = read_half chan in 
  let e_version = read_word chan in 
  let e_entry = read_addr chan in
  let e_phoff = read_off chan in
  let e_shoff = read_off chan in
  let e_flags = read_word chan in
  let e_ehsize = read_half chan in 
  let e_phentsize = read_half chan in
  let e_phnum = read_half chan in
  let e_shentsize = read_half chan in
  let e_shnum = read_half chan in
  let e_shstrndx = read_half chan in
  {
    e_ident = e_ident;
    e_type =  e_type;
    e_machine = e_machine;
    e_version = e_version;
    e_entry = e_entry;
    e_phoff = e_phoff;
    e_shoff = e_shoff;
    e_flags = e_flags;
    e_ehsize = e_ehsize;
    e_phentsize = e_phentsize;
    e_phnum = e_phnum;
    e_shentsize = e_shentsize;
    e_shnum = e_shnum;
    e_shstrndx = e_shstrndx;
  };;

let print_file_header fh = 
  Printf.printf "Type: %i\n" (Int64.to_int fh.e_type);
  Printf.printf "Machine: %i\n" (Int64.to_int fh.e_machine);
  Printf.printf "Version: 0x%x\n" (Int64.to_int fh.e_version);
  Printf.printf "Entry point address: 0x%x\n" (Int64.to_int fh.e_entry);
  Printf.printf "Size of this header: %i bytes\n" (Int64.to_int fh.e_ehsize);
  Printf.printf "Size of program headers: %i bytes\n" (Int64.to_int fh.e_phentsize);
  Printf.printf "Number of program headers: %i\n" (Int64.to_int fh.e_phnum);
  Printf.printf "Size of section headers: %i bytes\n" (Int64.to_int fh.e_shentsize);
  Printf.printf "Number of section headers: %i\n" (Int64.to_int fh.e_shnum);
  Printf.printf "Section header string table index: %i\n" (Int64.to_int fh.e_shstrndx)
;;

type section_header = { 
  sh_name: elf_word;            (* Section name (string tbl index) *)
  sh_type: elf_word;            (* Section type *)
  sh_flags: elf_word;           (* Section flags *)
  sh_addr: elf_addr;            (* Section virtual addr at execution *)
  sh_offset:elf_off;            (* Section file offset *)
  sh_size: elf_word;            (* Section size in bytes *)
  sh_link: elf_word;            (* Link to another section *)
  sh_info: elf_word;            (* Additional section information *)
  sh_addralign: elf_word;       (* Section alignment *)
  sh_entsize: elf_word;         (* Entry size if section holds table *)
};;

let read_section_header chan : section_header = 
  let sh_name = read_word chan in
  let sh_type = read_word chan in
  let sh_flags = read_word chan in
  let sh_addr = read_addr chan in
  let sh_offset = read_off chan in
  let sh_size = read_word chan in
  let sh_link = read_word chan in
  let sh_info = read_word chan in
  let sh_addralign = read_word chan in
  let sh_entsize = read_word chan in
  {
    sh_name = sh_name;
    sh_type = sh_type;
    sh_flags = sh_flags;
    sh_addr = sh_addr;
    sh_offset = sh_offset;
    sh_size = sh_size;
    sh_link = sh_link;
    sh_info = sh_info;
    sh_addralign = sh_addralign;
    sh_entsize = sh_entsize;
  }

let crap = Int64.to_int 

let goto_section_table chan fh = seek_in chan (crap fh.e_shoff);;
let goto_next_section chan fh = seek_in chan (Int64.to_int fh.e_shentsize);;
let goto_section_x chan fh x =
  seek_in chan ((crap fh.e_shoff) + x * ((Int64.to_int fh.e_shentsize)))
;;

let get_string chan fh idx = 
  goto_section_x chan fh (Int64.to_int fh.e_shstrndx);
  let s = read_section_header chan in
  seek_in chan ((crap s.sh_offset) + idx);
  let rec read_list l = 
    let c = input_char chan in
    if (Char.code c) = 0 then List.rev (c :: l)
    else read_list (c :: l)
  in
  read_list []
;;  
  
let print_string l = List.iter (Printf.printf "%c") l;; 

let main () = 
  let elf = 
    try open_in_bin Sys.argv.(1) 
    with 
      | Sys_error _ -> failwith "Cannot open file"
  in
  let fh = read_file_header elf in
  print_file_header fh;

  Printf.printf "\n\n\n";
  Printf.printf "Start of section header: %x\n" (Int64.to_int fh.e_shoff);

  goto_section_table elf fh;
  Printf.printf "position: %i\n" (pos_in elf);
  goto_section_x elf fh 2;
  Printf.printf "position: %i\n" (pos_in elf);
  let s = read_section_header elf in
  Printf.printf "size of .text: %x\n" (Int64.to_int s.sh_size);
  Printf.printf "Section name: "; 
  print_string (get_string elf fh (Int64.to_int s.sh_name));
  print_newline()
;;

main ()
