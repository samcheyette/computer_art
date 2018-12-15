alphabet = "abc"
def babel(length, books=[""]):
	if length <= 0:
		return books
	else:
		new_books = []
		for letter in alphabet:
			for book in books:
				new_books.append(book + letter)
		return babel(length-1, new_books)

print babel(7)
# prints:  ['aaaaaaa', 'baaaaaa', 'caaaaaa',..., 
#           'acccccc', 'bcccccc', 'ccccccc']
