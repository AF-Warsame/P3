//////////////////////////////////////////////////////////////////////
//    MemManager.java
//    CS323 MP3
/////////////////////////////////////////////////////////////////////

public class MemManager {

    public static final int NumSwapPages = 4096;

    /* Replacement Policy */
    public static final int ESC = 0;
    public static final int LRU = 1;
    public static final int FIFO = 2;

    /* private members */
    private List pageBuffer;     // Page Buffer queue
    private int buffersize;

    private BitMap coreFreeMap;
    private BitMap swapFreeMap;
    private BitMap swapValidMap;
    private TranslationEntry[] coreOwners;
    private TranslationEntry[] swapOwners;

    private int[] queue;      // for ESC and FIFO
    private int queueCounter; // revolving counter for ESC and FIFO

    private OpenFile swapfile;
    private Semaphore mutex;
    private Lock test;

    private int hbits;
    private int bitMask;
    private int lruUseBit;
    private int counter;           // for LRU

    private int[] history;         // for LRU
    private Timer history_timer;   // for LRU

    private int policy;
    private int formatCounter;


    MemManager(int pbuffer_in, int hbits_in) {
        formatCounter = 0;

        coreFreeMap = new BitMap(Machine.NumPhysPages);
        coreOwners  = new TranslationEntry[Machine.NumPhysPages];

        swapFreeMap  = new BitMap(NumSwapPages);
        swapValidMap = new BitMap(NumSwapPages);
        swapOwners   = new TranslationEntry[NumSwapPages];

        for (int i = 0; i < Machine.NumPhysPages; i++)      coreOwners[i] = null;
        for (int i = 0; i < NumSwapPages; i++)              swapOwners[i] = null;

        mutex = new Semaphore("memMgr", 1);

        Debug.ASSERT(Nachos.fileSystem != null);
        Debug.ASSERT(Nachos.fileSystem.create("nachos.bs", 0));
        swapfile = Nachos.fileSystem.open("nachos.bs");
        Debug.ASSERT(swapfile != null);

        buffersize = pbuffer_in;
        if (buffersize > 0) {
            pageBuffer = new List();
            for (int i = 0; i < buffersize; i++) {
                int page = Machine.NumPhysPages - i - 1;
                pageBuffer.append(new Integer(page));
                coreFreeMap.mark(page);
            }
        }

        hbits = hbits_in;
        if (hbits > 0) {
            bitMask   = (1 << hbits) - 1;
            lruUseBit = 1 << (hbits - 1);
            history   = new int[Machine.NumPhysPages];
            new Timer(new PageTimer(), false, false);
            policy    = LRU;

        } else if (hbits < 0) {
            queue = new int[Machine.NumPhysPages - buffersize];
            for (int i = 0; i < queue.length; i++) queue[i] = i;
            queueCounter = 0;
            policy       = FIFO;

        } else {
            queue = new int[Machine.NumPhysPages - buffersize];
            for (int i = 0; i < queue.length; i++) queue[i] = i;
            queueCounter = 0;
            policy       = ESC;
        }

        counter = 0;
    }

    int memAvail() {
        return coreFreeMap.numClear() + swapFreeMap.numClear();
    }

    void clear(TranslationEntry[] pageTable, int numPages) {
        int swapFrame;
        for (int i = 0; i < numPages; i++) {
            if (pageTable[i].legal) {
                if (pageTable[i].valid) {
                    coreFreeMap.clear(pageTable[i].physicalPage);
                    coreOwners[pageTable[i].physicalPage] = null;
                } else if ((swapFrame = swapSearch(pageTable[i])) != -1) {
                    swapFreeMap.clear(swapFrame);
                    swapValidMap.clear(swapFrame);
                    swapOwners[swapFrame] = null;
                }
            }
        }
    }

    int locateFirst() {
        return coreFreeMap.find();
    }

    boolean InBuffer(int target) {
        for (int i = 0; i < buffersize; i++) {
            Integer f = (Integer) pageBuffer.viewElementAt(i);
            if (f.intValue() == target) return true;
        }
        return false;
    }

    int makeFreeFrame() {
        int frame = coreFreeMap.find();
        if (frame >= 0) {
            coreFreeMap.mark(frame);
            return frame;
        }

        int victim = -1;
        if (policy == FIFO) {
            victim = queue[queueCounter];
            queueCounter = (queueCounter + 1) % queue.length;

        } else if (policy == LRU) {
            int start = counter, min = Integer.MAX_VALUE;
            for (int k = 0; k < Machine.NumPhysPages; k++) {
                int f = (start + k) % Machine.NumPhysPages;
                if (!coreFreeMap.test(f) && history[f] < min) {
                    min = history[f];
                    victim = f;
                }
            }
            counter = (victim + 1) % Machine.NumPhysPages;

        } else { // ESC
            outer:
            for (int pass = 0; pass < 4; pass++) {
                for (int i = 0; i < queue.length; i++) {
                    int idx = (queueCounter + i) % queue.length;
                    int f = queue[idx];
                    TranslationEntry te = coreOwners[f];
                    int cls = (te.use ? 2 : 0) + (te.dirty ? 1 : 0);
                    if (cls == pass) {
                        victim = f;
                        queueCounter = (idx + 1) % queue.length;
                        Machine.pageTable[te.virtualPage].use = false;
                        break outer;
                    }
                }
            }
        }
        return victim;
    }

    void faultIn(TranslationEntry PTEntry) {
        int physPage = makeFreeFrame();
        if (coreOwners[physPage] != null && coreOwners[physPage].dirty) {
            pageOut(physPage);
        } else if (coreOwners[physPage] != null) {
            coreOwners[physPage].valid = false;
        }
        pageIn(PTEntry, physPage);
    }

    void recordHistory(int arg) {
        for (int f = 0; f < Machine.NumPhysPages; f++) {
            if (!coreFreeMap.test(f)) {
                history[f] = (history[f] >>> 1) & bitMask;
                int vpn = coreOwners[f].virtualPage;
                if (Machine.pageTable[vpn].use) {
                    history[f] |= lruUseBit;
                    Machine.pageTable[vpn].use = false;
                }
            }
        }
    }

    void pageIn(TranslationEntry PTEntry, int physFrame) {
        int sf = swapSearch(PTEntry);
        byte[] buf = new byte[Machine.PageSize];

        if (sf >= 0) {
            swapfile.readAt(buf, 0, Machine.PageSize, Machine.PageSize * sf);
            swapFreeMap.clear(sf);
            swapValidMap.clear(sf);
            swapOwners[sf] = null;
        } else {
            NachosThread.thisThread().space.readSourcePage(buf, PTEntry.virtualPage);
        }

        for (int x = 0; x < Machine.PageSize; x++) {
            Machine.writeMem(
                PTEntry.virtualPage * Machine.PageSize + x,
                1,
                buf[x]
            );
        }

        PTEntry.physicalPage = physFrame;
        PTEntry.valid       = true;
        PTEntry.use         = false;
        PTEntry.dirty       = false;
        coreOwners[physFrame] = PTEntry;
        coreFreeMap.mark(physFrame);

        if (policy == LRU) history[physFrame] = 0;
    }

    void pageOut(int physFrame) {
        TranslationEntry te = coreOwners[physFrame];
        int[] ibuf = new int[Machine.PageSize];
        byte[] cbuf = new byte[Machine.PageSize];

        te.valid = true;
        try {
            for (int i = 0; i < Machine.PageSize; i++) {
                ibuf[i] = Machine.readMem(
                    te.virtualPage * Machine.PageSize + i, 1
                );
            }
        } catch (Exception e) {
            System.out.println("Exception reading memory");
        }
        te.valid = false;

        for (int i = 0; i < Machine.PageSize; i++) {
            cbuf[i] = (byte) ibuf[i];
        }

        int slot;
        for (slot = 0; slot < NumSwapPages && swapOwners[slot] != te; slot++);
        if (slot == NumSwapPages) {
            slot = swapFreeMap.find();
            Debug.ASSERT(slot >= 0);
            swapOwners[slot] = te;
        } else {
            swapFreeMap.mark(slot);
        }

        int wrote = swapfile.writeAt(
            cbuf, 0, Machine.PageSize, Machine.PageSize * slot
        );
        Debug.ASSERT(wrote == Machine.PageSize);

        te.dirty = false;
        te.valid = false;
    }

    void pageFaultExceptionHandler(int vaddr) {
        mutex.P();
        int vpn = vaddr / Machine.PageSize;
        TranslationEntry e = Machine.pageTable[vpn];
        if (e == null || !e.legal) {
            // Simplest halt if illegal
            System.out.println("Illegal page fault at vaddr=" + vaddr);
            KThread.currentThread().finish();
        }
        faultIn(e);
        mutex.V();
    }

    int swapSearch(TranslationEntry PTEntry) {
        for (int i = 0; i < NumSwapPages; i++) {
            if (swapOwners[i] == PTEntry) return i;
        }
        return -1;
    }

    // Stub for VMTest
    public void display() {
        System.out.println("MemManager.display() called.");
    }

} // end of MemManager


Alter fro K thread to nachos pls
