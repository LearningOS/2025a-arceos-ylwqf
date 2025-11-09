#![no_std]

use allocator::{BaseAllocator, ByteAllocator, PageAllocator};

/// Early memory allocator
/// Use it before formal bytes-allocator and pages-allocator can work!
/// This is a double-end memory range:
/// - Alloc bytes forward
/// - Alloc pages backward
///
/// [ bytes-used | avail-area | pages-used ]
/// |            | -->    <-- |            |
/// start       b_pos        p_pos       end
///
/// For bytes area, 'count' records number of allocations.
/// When it goes down to ZERO, free bytes-used area.
/// For pages area, it will never be freed!
///
pub struct EarlyAllocator<const SIZE: usize> {
    start: usize,
    end: usize,
    b_pos: usize,
    p_pos: usize,
    count: usize,
}

impl<const SIZE: usize> EarlyAllocator<SIZE> {
    pub const fn new() -> Self {
        Self {
            start: 0,
            end: 0,
            b_pos: 0,
            p_pos: 0,
            count: 0,
        }
    }
}

impl<const SIZE: usize> BaseAllocator for EarlyAllocator<SIZE> {
    fn init(&mut self, start: usize, size: usize) {
        self.start = start;
        let end = start + size;
        self.end = end;
        self.b_pos = start;
        self.p_pos = end;
        self.count = 0;
    }

    fn add_memory(&mut self, _start: usize, _size: usize) -> allocator::AllocResult {
        Err(allocator::AllocError::NoMemory)
    }
}

impl<const SIZE: usize> ByteAllocator for EarlyAllocator<SIZE> {
    fn alloc(
        &mut self,
        layout: core::alloc::Layout,
    ) -> allocator::AllocResult<core::ptr::NonNull<u8>> {
        let align = layout.align();
        let size = layout.size();

        // `Layout::align()` for a valid Layout is always >= 1 and a power of two.
        // We assert that here and then use the standard bit trick to align up.
        debug_assert!(align != 0 && align.is_power_of_two());
        // align up current b_pos
        let alloc_start = (self.b_pos + align - 1) & !(align - 1);

        let new_b_pos = match alloc_start.checked_add(size) {
            Some(v) => v,
            None => return Err(allocator::AllocError::NoMemory),
        };

        if new_b_pos > self.p_pos {
            return Err(allocator::AllocError::NoMemory);
        }

        self.b_pos = new_b_pos;
        Ok(unsafe { core::ptr::NonNull::new_unchecked(alloc_start as *mut u8) })
    }

    fn dealloc(&mut self, pos: core::ptr::NonNull<u8>, layout: core::alloc::Layout) {
        let _ = (pos, layout);
        // simple reference-count style: when count reaches zero, reclaim bytes
        if self.count > 0 {
            self.count -= 1;
            if self.count == 0 {
                self.b_pos = self.start;
            }
        }
    }

    fn total_bytes(&self) -> usize {
        self.end.saturating_sub(self.start)
    }

    fn used_bytes(&self) -> usize {
        self.b_pos.saturating_sub(self.start)
    }

    fn available_bytes(&self) -> usize {
        if self.p_pos > self.b_pos {
            self.p_pos - self.b_pos
        } else {
            0
        }
    }
}

impl<const SIZE: usize> PageAllocator for EarlyAllocator<SIZE> {
    const PAGE_SIZE: usize = SIZE;

    fn alloc_pages(
        &mut self,
        num_pages: usize,
        align_pow2: usize,
    ) -> allocator::AllocResult<usize> {
        if num_pages == 0 {
            return Err(allocator::AllocError::InvalidParam);
        }
        // align_pow2 is given in bytes; require it to be multiple of PAGE_SIZE
        if align_pow2 % Self::PAGE_SIZE != 0 {
            return Err(allocator::AllocError::InvalidParam);
        }
        let align_pages = align_pow2 / Self::PAGE_SIZE;
        if !is_power_of_two(align_pages) {
            return Err(allocator::AllocError::InvalidParam);
        }

        let page_size = Self::PAGE_SIZE;
        let size_bytes = match num_pages.checked_mul(page_size) {
            Some(s) => s,
            None => return Err(allocator::AllocError::NoMemory),
        };

        if self.p_pos < size_bytes {
            return Err(allocator::AllocError::NoMemory);
        }

        let raw = self.p_pos - size_bytes;
        let align_bytes = align_pages * page_size;
        let alloc_start = align_down(raw, align_bytes);
        if alloc_start < self.b_pos {
            return Err(allocator::AllocError::NoMemory);
        }
        self.p_pos = alloc_start;
        Ok(self.p_pos)
    }

    fn dealloc_pages(&mut self, pos: usize, num_pages: usize) {
        let _ = (pos, num_pages);
        // EarlyAllocator does not reclaim pages once allocated.
    }

    fn total_pages(&self) -> usize {
        (self.end.saturating_sub(self.start)) / Self::PAGE_SIZE
    }

    fn used_pages(&self) -> usize {
        (self.end.saturating_sub(self.p_pos)) / Self::PAGE_SIZE
    }

    fn available_pages(&self) -> usize {
        if self.p_pos > self.b_pos {
            (self.p_pos - self.b_pos) / Self::PAGE_SIZE
        } else {
            0
        }
    }
}

// helpers
const fn is_power_of_two(x: usize) -> bool {
    x != 0 && (x & (x - 1)) == 0
}

const fn align_down(addr: usize, align: usize) -> usize {
    if align == 0 {
        addr
    } else {
        addr & !(align - 1)
    }
}
