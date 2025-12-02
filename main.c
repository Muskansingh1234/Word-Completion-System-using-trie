/*
 * Word Completion System (improved, safe, UTF-8)
 *
 * Features:
 *  - Trie-based autocomplete using wchar_t (UTF-8 support via locale)
 *  - Case-insensitive search/insert
 *  - Word frequency ranking (increments on insert/search/select)
 *  - Dictionary text load/save (UTF-8), and binary trie save/load
 *  - Top-K frequent words
 *  - Delete with pruning
 *  - Spell suggestions (Levenshtein)
 *  - Autocomplete suggestions (top-K) and interactive selection
 *
 * Compile:
 *  gcc -Wall -Wextra -Wpedantic -O2 -o word_completion word_completion.c
 */

#define _XOPEN_SOURCE 700
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <wchar.h>
#include <wctype.h>
#include <locale.h>
#include <errno.h>

#define MAX_WORD_LEN 512        /* max wide chars per word (including NUL) */
#define TOP_K 10
#define INITIAL_CAP 256

/* default filenames (narrow) */
#define DICT_TEXT_FILENAME "words.txt"
#define DICT_BIN_FILENAME  "words.txt.bin"

typedef struct ChildNode ChildNode;
typedef struct TrieNode TrieNode;

struct ChildNode {
    wchar_t ch;
    TrieNode *child;
    ChildNode *next;
};

struct TrieNode {
    int isEnd;
    int frequency;
    ChildNode *children;
};

/* ---------- Utility: safe memory helpers ---------- */

static void *xmalloc(size_t s) {
    void *p = malloc(s);
    if (!p) {
        fprintf(stderr, "malloc failed (size=%zu)\n", s);
        exit(EXIT_FAILURE);
    }
    return p;
}

static void *xrealloc(void *ptr, size_t s) {
    void *t = realloc(ptr, s);
    if (!t) {
        fprintf(stderr, "realloc failed (size=%zu)\n", s);
        exit(EXIT_FAILURE);
    }
    return t;
}

/* ---------- Trie creation / free ---------- */

TrieNode *create_node(void) {
    TrieNode *n = (TrieNode *)xmalloc(sizeof(TrieNode));
    n->isEnd = 0;
    n->frequency = 0;
    n->children = NULL;
    return n;
}

void free_subtree(TrieNode *node) {
    if (!node) return;
    ChildNode *c = node->children;
    while (c) {
        ChildNode *next = c->next;
        free_subtree(c->child);
        free(c);
        c = next;
    }
    free(node);
}

/* ---------- Child helpers (linked-list) ---------- */

ChildNode *find_child(const TrieNode *node, wchar_t ch) {
    ChildNode *cur = node->children;
    while (cur) {
        if (cur->ch == ch) return cur;
        cur = cur->next;
    }
    return NULL;
}

ChildNode *add_child(TrieNode *node, wchar_t ch) {
    /* add at head (fast). Caller uses returned ChildNode->child as next TrieNode */
    ChildNode *cn = (ChildNode *)xmalloc(sizeof(ChildNode));
    cn->ch = ch;
    cn->child = create_node();
    cn->next = node->children;
    node->children = cn;
    return cn;
}

/* ---------- Insert / Search / Delete ---------- */

void insert_word(TrieNode *root, const wchar_t *w) {
    TrieNode *cur = root;
    for (size_t i = 0; w[i] != L'\0'; ++i) {
        wchar_t ch = towlower(w[i]);
        ChildNode *c = find_child(cur, ch);
        if (!c) c = add_child(cur, ch);
        cur = c->child;
    }
    cur->isEnd = 1;
    cur->frequency += 1;
}

TrieNode *search_node(TrieNode *root, const wchar_t *w) {
    TrieNode *cur = root;
    for (size_t i = 0; w[i] != L'\0'; ++i) {
        wchar_t ch = towlower(w[i]);
        ChildNode *c = find_child(cur, ch);
        if (!c) return NULL;
        cur = c->child;
    }
    if (cur->isEnd) return cur;
    return NULL;
}

int delete_word(TrieNode *root, const wchar_t *w) {
    /* iterative stack of (parent node, child link) */
    typedef struct { TrieNode *parent; ChildNode *link; } StackEntry;
    StackEntry stack[MAX_WORD_LEN];
    int sp = 0;
    TrieNode *cur = root;
    for (size_t i = 0; w[i] != L'\0'; ++i) {
        wchar_t ch = towlower(w[i]);
        ChildNode *c = find_child(cur, ch);
        if (!c) return 0; /* not found */
        stack[sp].parent = cur;
        stack[sp].link = c;
        sp++;
        cur = c->child;
    }
    if (!cur->isEnd) return 0;
    cur->isEnd = 0;
    cur->frequency = 0;

    /* prune bottom-up */
    while (sp > 0) {
        StackEntry top = stack[--sp];
        TrieNode *parent = top.parent;
        ChildNode *link = top.link;
        TrieNode *childnode = link->child;
        if (childnode->isEnd || childnode->children != NULL) break;
        /* remove link from parent's linked list */
        ChildNode *iter = parent->children;
        ChildNode *prev = NULL;
        while (iter && iter != link) { prev = iter; iter = iter->next; }
        if (!iter) break; /* not found; should not happen */
        if (prev) prev->next = iter->next;
        else parent->children = iter->next;
        free(childnode);
        free(iter);
    }
    return 1;
}

/* ---------- Collect words DFS (wide buffer) ---------- */

typedef struct {
    wchar_t *word; /* allocated via wcsdup style */
    int freq;
} FullWord;

static FullWord *allwords = NULL;
static int allwords_cnt = 0;
static int allwords_cap = 0;

static void ensure_allwords_cap(int cap) {
    if (allwords_cap >= cap) return;
    int newcap = (allwords_cap == 0) ? INITIAL_CAP : allwords_cap * 2;
    while (newcap < cap) newcap *= 2;
    allwords = (FullWord *)xrealloc(allwords, newcap * sizeof(FullWord));
    allwords_cap = newcap;
}

static wchar_t *wcsdup_alloc(const wchar_t *s) {
    if (!s) return NULL;
    size_t n = wcslen(s);
    wchar_t *p = (wchar_t *)xmalloc((n + 1) * sizeof(wchar_t));
    wcscpy(p, s);
    return p;
}

void dfs_collect_all(TrieNode *node, wchar_t *buffer, int depth) {
    if (!node) return;
    if (node->isEnd) {
        buffer[depth] = L'\0';
        ensure_allwords_cap(allwords_cnt + 1);
        allwords[allwords_cnt].word = wcsdup_alloc(buffer);
        allwords[allwords_cnt].freq = node->frequency;
        allwords_cnt++;
    }
    ChildNode *c = node->children;
    while (c) {
        buffer[depth] = c->ch;
        dfs_collect_all(c->child, buffer, depth + 1);
        c = c->next;
    }
}

FullWord *get_all_words(TrieNode *root, int *out_count) {
    allwords_cnt = 0;
    if (!root) { *out_count = 0; return NULL; }
    wchar_t buffer[MAX_WORD_LEN];
    dfs_collect_all(root, buffer, 0);
    *out_count = allwords_cnt;
    return allwords;
}

void free_allwords(void) {
    if (!allwords) return;
    for (int i = 0; i < allwords_cnt; ++i) free(allwords[i].word);
    free(allwords);
    allwords = NULL;
    allwords_cnt = 0;
    allwords_cap = 0;
}

/* ---------- Autocomplete suggestions ---------- */

static FullWord *suggestions = NULL;
static int sugg_cnt = 0;
static int sugg_cap = 0;

static void ensure_sugg_cap(int cap) {
    if (sugg_cap >= cap) return;
    int newcap = (sugg_cap == 0) ? INITIAL_CAP : sugg_cap * 2;
    while (newcap < cap) newcap *= 2;
    suggestions = (FullWord *)xrealloc(suggestions, newcap * sizeof(FullWord));
    sugg_cap = newcap;
}

/* collect words under a node into suggestions array using a provided prefix buffer */
void dfs_collect_sugg(TrieNode *node, wchar_t *buffer, int depth) {
    if (!node) return;
    if (node->isEnd) {
        buffer[depth] = L'\0';
        ensure_sugg_cap(sugg_cnt + 1);
        suggestions[sugg_cnt].word = wcsdup_alloc(buffer);
        suggestions[sugg_cnt].freq = node->frequency;
        sugg_cnt++;
    }
    ChildNode *c = node->children;
    while (c) {
        buffer[depth] = c->ch;
        dfs_collect_sugg(c->child, buffer, depth + 1);
        c = c->next;
    }
}

/* find prefix node */
TrieNode *find_prefix_node(TrieNode *root, const wchar_t *prefix) {
    TrieNode *cur = root;
    for (size_t i = 0; prefix[i] != L'\0'; ++i) {
        wchar_t ch = towlower(prefix[i]);
        ChildNode *c = find_child(cur, ch);
        if (!c) return NULL;
        cur = c->child;
    }
    return cur;
}

/* compare by freq desc, then lexicographic */
int compare_fullword_desc(const void *a, const void *b) {
    const FullWord *fa = (const FullWord *)a;
    const FullWord *fb = (const FullWord *)b;
    if (fb->freq > fa->freq) return 1;
    if (fb->freq < fa->freq) return -1;
    return wcscoll(fa->word, fb->word);
}

/* returns number of suggestions; out pointer will point to suggestions array (owned by module) */
int autocomplete(TrieNode *root, const wchar_t *prefix, FullWord **out) {
    sugg_cnt = 0;
    suggestions = suggestions; /* no-op for clarity */
    TrieNode *node = find_prefix_node(root, prefix);
    if (!node) { *out = NULL; return 0; }
    wchar_t buffer[MAX_WORD_LEN];
    /* copy prefix to buffer (lowercase) */
    size_t plen = wcslen(prefix);
    if (plen >= MAX_WORD_LEN - 1) plen = MAX_WORD_LEN - 2;
    for (size_t i = 0; i < plen; ++i) buffer[i] = towlower(prefix[i]);
    dfs_collect_sugg(node, buffer, (int)plen);
    if (sugg_cnt > 1) qsort(suggestions, sugg_cnt, sizeof(FullWord), compare_fullword_desc);
    *out = suggestions;
    return sugg_cnt;
}

/* freers suggestions array contents (words) but keeps buffer for reuse */
void free_suggestions(void) {
    if (!suggestions) return;
    for (int i = 0; i < sugg_cnt; ++i) free(suggestions[i].word);
    free(suggestions);
    suggestions = NULL;
    sugg_cnt = 0;
    sugg_cap = 0;
}

/* show suggestions and allow selection to accept which increases freq (or insert if not present) */
void show_suggestions_and_choose(TrieNode *root, FullWord *sugs, int count, int topn) {
    int limit = (count < topn) ? count : topn;
    if (limit == 0) {
        wprintf(L"No suggestions.\n");
        return;
    }
    wprintf(L"Suggestions:\n");
    for (int i = 0; i < limit; ++i) {
        wprintf(L"%d. %ls  (%d)\n", i + 1, sugs[i].word, sugs[i].freq);
    }
    wprintf(L"Select suggestion number to accept (0 to cancel): ");
    char line[64];
    if (!fgets(line, sizeof(line), stdin)) { wprintf(L"Input error.\n"); return; }
    int sel = atoi(line);
    if (sel <= 0 || sel > limit) {
        wprintf(L"Cancelled.\n");
        return;
    }
    wchar_t *chosen = sugs[sel - 1].word;
    TrieNode *node = search_node(root, chosen);
    if (node) {
        node->frequency += 1;
        wprintf(L"Chosen: %ls (new freq %d)\n", chosen, node->frequency);
    } else {
        insert_word(root, chosen);
        wprintf(L"Inserted chosen word: %ls\n", chosen);
    }
}

/* ---------- Levenshtein distance (wide-char) ---------- */

static int min3(int a, int b, int c) {
    int m = a < b ? a : b;
    return (m < c) ? m : c;
}

int levenshtein(const wchar_t *s1, const wchar_t *s2) {
    int n = (int)wcslen(s1);
    int m = (int)wcslen(s2);
    if (n == 0) return m;
    if (m == 0) return n;
    int *v0 = (int *)xmalloc((m + 1) * sizeof(int));
    int *v1 = (int *)xmalloc((m + 1) * sizeof(int));
    for (int j = 0; j <= m; ++j) v0[j] = j;
    for (int i = 1; i <= n; ++i) {
        v1[0] = i;
        for (int j = 1; j <= m; ++j) {
            int cost = (s1[i - 1] == s2[j - 1]) ? 0 : 1;
            v1[j] = min3(v1[j - 1] + 1, v0[j] + 1, v0[j - 1] + cost);
        }
        int *tmp = v0; v0 = v1; v1 = tmp;
    }
    int dist = v0[m];
    free(v0); free(v1);
    return dist;
}

/* ---------- Spell suggestions ---------- */

typedef struct {
    wchar_t *word;
    int freq;
    int dist;
} DistEntry;

int compare_dist_entry(const void *a, const void *b) {
    const DistEntry *da = (const DistEntry *)a;
    const DistEntry *db = (const DistEntry *)b;
    if (da->dist != db->dist) return da->dist - db->dist;
    if (da->freq != db->freq) return db->freq - da->freq; /* higher freq earlier */
    return wcscoll(da->word, db->word);
}

void spell_suggest(TrieNode *root, const wchar_t *input, int topn) {
    int total = 0;
    FullWord *arr = get_all_words(root, &total);
    if (total == 0) {
        wprintf(L"No words to compare.\n");
        return;
    }
    DistEntry *darr = (DistEntry *)xmalloc(total * sizeof(DistEntry));
    for (int i = 0; i < total; ++i) {
        darr[i].word = arr[i].word; /* ownership still with allwords; we won't free here */
        darr[i].freq = arr[i].freq;
        darr[i].dist = levenshtein(input, arr[i].word);
    }
    qsort(darr, total, sizeof(DistEntry), compare_dist_entry);
    wprintf(L"Spell suggestions for \"%ls\":\n", input);
    for (int i = 0; i < total && i < topn; ++i) {
        wprintf(L"%d. %ls (dist=%d, freq=%d)\n", i + 1, darr[i].word, darr[i].dist, darr[i].freq);
    }
    free(darr);
    free_allwords();
}

/* ---------- Save/Load Trie (binary) ---------- */

static void write_uint32(FILE *f, uint32_t v) {
    if (fwrite(&v, sizeof(uint32_t), 1, f) != 1) { perror("fwrite"); exit(EXIT_FAILURE); }
}
static uint32_t read_uint32(FILE *f) {
    uint32_t v;
    if (fread(&v, sizeof(uint32_t), 1, f) != 1) { perror("fread"); exit(EXIT_FAILURE); }
    return v;
}

void save_node_binary(FILE *f, TrieNode *node) {
    if (!node) {
        int zero = 0;
        if (fwrite(&zero, sizeof(int), 1, f) != 1) { perror("fwrite"); exit(EXIT_FAILURE); }
        if (fwrite(&zero, sizeof(int), 1, f) != 1) { perror("fwrite"); exit(EXIT_FAILURE); }
        if (fwrite(&zero, sizeof(int), 1, f) != 1) { perror("fwrite"); exit(EXIT_FAILURE); }
        return;
    }
    if (fwrite(&node->isEnd, sizeof(int), 1, f) != 1) { perror("fwrite"); exit(EXIT_FAILURE); }
    if (fwrite(&node->frequency, sizeof(int), 1, f) != 1) { perror("fwrite"); exit(EXIT_FAILURE); }
    int cnt = 0;
    ChildNode *c = node->children;
    while (c) { cnt++; c = c->next; }
    if (fwrite(&cnt, sizeof(int), 1, f) != 1) { perror("fwrite"); exit(EXIT_FAILURE); }
    c = node->children;
    while (c) {
        uint32_t code = (uint32_t)c->ch;
        write_uint32(f, code);
        save_node_binary(f, c->child);
        c = c->next;
    }
}

int save_trie_binary(const char *filename, TrieNode *root) {
    FILE *f = fopen(filename, "wb");
    if (!f) { perror("fopen"); return 0; }
    save_node_binary(f, root);
    fclose(f);
    return 1;
}

TrieNode *load_node_binary(FILE *f) {
    int isEnd;
    if (fread(&isEnd, sizeof(int), 1, f) != 1) {
        return NULL;
    }
    int frequency;
    if (fread(&frequency, sizeof(int), 1, f) != 1) { perror("fread"); exit(EXIT_FAILURE); }
    int cnt;
    if (fread(&cnt, sizeof(int), 1, f) != 1) { perror("fread"); exit(EXIT_FAILURE); }
    TrieNode *node = create_node();
    node->isEnd = isEnd;
    node->frequency = frequency;
    for (int i = 0; i < cnt; ++i) {
        uint32_t code;
        if (fread(&code, sizeof(uint32_t), 1, f) != 1) { perror("fread"); exit(EXIT_FAILURE); }
        TrieNode *childNode = load_node_binary(f);
        if (!childNode) { fprintf(stderr, "Error loading child node\n"); exit(EXIT_FAILURE); }
        ChildNode *cn = (ChildNode *)xmalloc(sizeof(ChildNode));
        cn->ch = (wchar_t)code;
        cn->child = childNode;
        cn->next = node->children;
        node->children = cn;
    }
    return node;
}

int load_trie_binary(const char *filename, TrieNode **out_root) {
    FILE *f = fopen(filename, "rb");
    if (!f) return 0;
    TrieNode *n = load_node_binary(f);
    fclose(f);
    if (!n) return 0;
    *out_root = n;
    return 1;
}

/* ---------- Load dictionary text file (UTF-8) ---------- */

/* Helper: read line as multibyte and convert to wide */
int load_dictionary_text(const char *filename, TrieNode *root) {
    FILE *f = fopen(filename, "r");
    if (!f) { /* not fatal - may create empty trie */ return 0; }
    char mbline[4096];
    wchar_t wline[MAX_WORD_LEN];
    while (fgets(mbline, sizeof(mbline), f)) {
        size_t len = strlen(mbline);
        while (len > 0 && (mbline[len - 1] == '\n' || mbline[len - 1] == '\r')) { mbline[--len] = '\0'; }
        if (len == 0) continue;
        /* convert to wide using current locale */
        size_t need = mbstowcs(NULL, mbline, 0);
        if (need == (size_t)-1) continue; /* conversion failure */
        if (need >= MAX_WORD_LEN) need = MAX_WORD_LEN - 1;
        mbstowcs(wline, mbline, need + 1);
        /* lowercase and insert */
        for (size_t i = 0; wline[i] != L'\0'; ++i) wline[i] = towlower(wline[i]);
        insert_word(root, wline);
    }
    fclose(f);
    return 1;
}

/* write dictionary back to text file sorted lexicographically */
int write_dictionary_text(const char *filename, TrieNode *root) {
    int count = 0;
    FullWord *arr = get_all_words(root, &count);
    /* open file for writing (overwrite) */
    FILE *f = fopen(filename, "w");
    if (!f) { free_allwords(); return 0; }
    if (count == 0) {
        fclose(f); free_allwords(); return 1;
    }
    /* sort lexicographically */
    qsort(arr, count, sizeof(FullWord), 
        (int (*)(const void*, const void*)) ( (int(*)(const FullWord*, const FullWord*)) 
            (int(*)(const void*, const void*)) ( /* trick to avoid prototype mismatch */ wcscoll) ) );
    /* The above cast is ugly — instead we implement lex comparator below */
    /* We'll re-sort with proper comparator */
    int lex_cmp(const void *a, const void *b) {
        const FullWord *fa = (const FullWord *)a;
        const FullWord *fb = (const FullWord *)b;
        return wcscoll(fa->word, fb->word);
    }
    qsort(arr, count, sizeof(FullWord), lex_cmp);

    for (int i = 0; i < count; ++i) {
        /* convert wide to multibyte using wcstombs */
        size_t wlen = wcslen(arr[i].word);
        size_t maxbytes = (wlen + 1) * MB_CUR_MAX + 4;
        char *mb = (char *)xmalloc(maxbytes);
        size_t wrote = wcstombs(mb, arr[i].word, maxbytes);
        if (wrote == (size_t)-1) { free(mb); continue; }
        fprintf(f, "%s\n", mb);
        free(mb);
    }
    fclose(f);
    free_allwords();
    return 1;
}

/* ---------- Top-K frequent display ---------- */

int compare_fullword_freq(const void *a, const void *b) {
    const FullWord *fa = (const FullWord *)a;
    const FullWord *fb = (const FullWord *)b;
    if (fb->freq > fa->freq) return 1;
    if (fb->freq < fa->freq) return -1;
    return wcscoll(fa->word, fb->word);
}

void show_top_k(TrieNode *root, int k) {
    int count = 0;
    FullWord *arr = get_all_words(root, &count);
    if (count == 0) {
        wprintf(L"No words in dictionary.\n");
        return;
    }
    qsort(arr, count, sizeof(FullWord), compare_fullword_freq);
    wprintf(L"Top %d frequent words:\n", k);
    for (int i = 0; i < k && i < count; ++i) {
        wprintf(L"%d. %ls (%d)\n", i + 1, arr[i].word, arr[i].freq);
    }
    free_allwords();
}

/* ---------- CLI helpers ---------- */

int read_wline(wchar_t *buf, int maxlen) {
    if (!fgetws(buf, maxlen, stdin)) return 0;
    size_t len = wcslen(buf);
    if (len > 0 && buf[len - 1] == L'\n') buf[len - 1] = L'\0';
    return 1;
}

/* ---------- Main interactive program ---------- */

int main(int argc, char **argv) {
    /* set UTF-8 locale for proper multibyte <-> wide conversions and wide I/O */
    if (!setlocale(LC_CTYPE, "")) {
        fprintf(stderr, "Warning: locale not set; UTF-8 behaviour may be incorrect.\n");
    }

    /* create root */
    TrieNode *root = create_node();

    /* Try to load binary trie first; else load text dictionary */
    if (load_trie_binary(DICT_BIN_FILENAME, &root)) {
        wprintf(L"Loaded trie from binary file: %s\n", DICT_BIN_FILENAME);
    } else {
        if (load_dictionary_text(DICT_TEXT_FILENAME, root)) {
            wprintf(L"Loaded dictionary from text file: %s\n", DICT_TEXT_FILENAME);
        } else {
            wprintf(L"Starting with empty dictionary (no file loaded).\n");
        }
    }

    char line[256];
    wchar_t wline[MAX_WORD_LEN];

    while (1) {
        wprintf(L"\n==============================\n");
        wprintf(L" WORD COMPLETION SYSTEM (UTF-8)\n");
        wprintf(L"==============================\n");
        wprintf(L"1. Search Word\n");
        wprintf(L"2. Get Autocomplete Suggestions\n");
        wprintf(L"3. Insert New Word\n");
        wprintf(L"4. View Top 10 Frequent Words\n");
        wprintf(L"5. Save Trie (Binary)\n");
        wprintf(L"6. Load Trie (Binary)\n");
        wprintf(L"7. Delete Word\n");
        wprintf(L"8. Spell Suggest (Did you mean?)\n");
        wprintf(L"9. Exit\n");
        wprintf(L"Enter choice: ");
        if (!fgets(line, sizeof(line), stdin)) break;
        int choice = atoi(line);

        switch (choice) {
            case 1: /* Search Word */
                wprintf(L"Enter word to search: ");
                if (!read_wline(wline, MAX_WORD_LEN)) { wprintf(L"Input error.\n"); break; }
                for (size_t i = 0; wline[i] != L'\0'; ++i) wline[i] = towlower(wline[i]);
                {
                    TrieNode *node = search_node(root, wline);
                    if (node) {
                        node->frequency += 1;
                        wprintf(L"Word \"%ls\" found. Frequency now %d\n", wline, node->frequency);
                        /* persist update immediately to text to keep sorted file (optional) */
                        if (!write_dictionary_text(DICT_TEXT_FILENAME, root)) {
                            /* not fatal */
                        }
                    } else {
                        wprintf(L"Word \"%ls\" NOT found.\n", wline);
                    }
                }
                break;

            case 2: /* Autocomplete */
                wprintf(L"Enter prefix: ");
                if (!read_wline(wline, MAX_WORD_LEN)) { wprintf(L"Input error.\n"); break; }
                for (size_t i = 0; wline[i] != L'\0'; ++i) wline[i] = towlower(wline[i]);
                {
                    FullWord *sugs = NULL;
                    int count = autocomplete(root, wline, &sugs);
                    if (count == 0) {
                        wprintf(L"No suggestions for \"%ls\".\n", wline);
                    } else {
                        show_suggestions_and_choose(root, sugs, count, TOP_K);
                        /* persist changes (if any) */
                        if (!write_dictionary_text(DICT_TEXT_FILENAME, root)) {
                            /* not fatal */
                        }
                    }
                    /* free suggestion words and buffer */
                    free_suggestions();
                }
                break;

            case 3: /* Insert New Word */
                wprintf(L"Enter new word to insert: ");
                if (!read_wline(wline, MAX_WORD_LEN)) { wprintf(L"Input error.\n"); break; }
                for (size_t i = 0; wline[i] != L'\0'; ++i) wline[i] = towlower(wline[i]);
                insert_word(root, wline);
                if (!write_dictionary_text(DICT_TEXT_FILENAME, root)) {
                    wprintf(L"Warning: Could not write sorted dictionary to %s\n", DICT_TEXT_FILENAME);
                } else {
                    wprintf(L"Word inserted and %s updated (sorted).\n", DICT_TEXT_FILENAME);
                }
                break;

            case 4: /* View Top 10 */
                show_top_k(root, TOP_K);
                break;

            case 5: /* Save Trie Binary */
                if (save_trie_binary(DICT_BIN_FILENAME, root)) {
                    wprintf(L"Trie saved to binary file: %s\n", DICT_BIN_FILENAME);
                } else {
                    wprintf(L"Failed to save trie binary to %s\n", DICT_BIN_FILENAME);
                }
                break;

            case 6: /* Load Trie Binary */
                free_subtree(root);
                root = create_node();
                if (load_trie_binary(DICT_BIN_FILENAME, &root)) {
                    wprintf(L"Loaded binary trie from %s\n", DICT_BIN_FILENAME);
                } else {
                    wprintf(L"Failed to load binary trie from %s\nRecreating empty trie.\n", DICT_BIN_FILENAME);
                    /* root already empty */
                }
                break;

            case 7: /* Delete Word */
                wprintf(L"Enter word to delete: ");
                if (!read_wline(wline, MAX_WORD_LEN)) { wprintf(L"Input error.\n"); break; }
                for (size_t i = 0; wline[i] != L'\0'; ++i) wline[i] = towlower(wline[i]);
                if (delete_word(root, wline)) {
                    if (!write_dictionary_text(DICT_TEXT_FILENAME, root)) {
                        wprintf(L"Warning: Failed to persist dictionary after deletion to %s\n", DICT_TEXT_FILENAME);
                    }
                    wprintf(L"Word \"%ls\" deleted (if existed) and %s updated.\n", wline, DICT_TEXT_FILENAME);
                } else {
                    wprintf(L"Word \"%ls\" not found.\n", wline);
                }
                break;

            case 8: /* Spell Suggest */
                wprintf(L"Enter word for spell suggestion: ");
                if (!read_wline(wline, MAX_WORD_LEN)) { wprintf(L"Input error.\n"); break; }
                for (size_t i = 0; wline[i] != L'\0'; ++i) wline[i] = towlower(wline[i]);
                spell_suggest(root, wline, TOP_K);
                break;

            case 9:
                wprintf(L"Saving trie to %s and exiting...\n", DICT_BIN_FILENAME);
                save_trie_binary(DICT_BIN_FILENAME, root);
                free_subtree(root);
                /* free module globals */
                free_allwords();
                free_suggestions();
                return 0;

            default:
                wprintf(L"Invalid choice.\n");
                break;
        }
    }

    /* cleanup on EOF */
    save_trie_binary(DICT_BIN_FILENAME, root);
    free_subtree(root);
    free_allwords();
    free_suggestions();
    return 0;
}
